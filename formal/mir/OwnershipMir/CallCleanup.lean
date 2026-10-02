import OwnershipMir.CallControl

namespace OwnershipMir.Calls

theorem Execution.cleaning {n : Nat} {program : Program n}
    {before after : OwnershipMir.Configuration (n + 1) (Op (n + 1))}
    (run : Run Op.exec before after) (stack : List (Frame n)) :
    Execution program ⟨.cleaning before.code, before.state, stack⟩ ⟨.cleaning after.code, after.state, stack⟩ := by
  induction run with
  | refl => exact .refl _
  | step head tail ih => exact .step (.clean head) ih

theorem activation_exit {n : Nat} (state : State (n + 1)) : (activationScope n).exit state = emptyState n := by
  have slots : clearSlots (activationScope n).owners state.slots = fun _ => none := by
    funext i
    exact if_pos (List.mem_finRange i)
  simp only [Scope.exit, slots, emptyState]

/-- Scope ownership is the whole activation, not a supplied subset. Its actual
cleanup trace follows newest-root, reverse-field, enclosing-storage-last order. -/
theorem Function.cleanup_trace {n : Nat} {signature : Signature} {function : Function n}
    (admitted : (activationScope n).Admitted function.cleanupContext) {state : State (n + 1)}
    (typed : state.Typed signature function.cleanupContext) :
    OwnershipTrace ⟨function.cleanup, state⟩ ⟨.halt, emptyState n⟩
      ((activationScope n).cleanupOrder function.cleanupContext) := by
  simpa only [Function.cleanup, activation_exit] using Scope.exit_trace admitted typed

theorem Function.cleanup_returns {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (admitted : (activationScope n).Admitted function.cleanupContext) {state : State (n + 1)}
    (typed : state.Typed signature function.cleanupContext) (frame : Frame n) (stack : List (Frame n)) :
    Execution program ⟨.cleaning function.cleanup, state, frame :: stack⟩
      ⟨.body frame.next frame.cleanup, frame.state, stack⟩ :=
  (Execution.cleaning (function.cleanup_trace admitted typed).run _).trans (.step .retire (.refl _))

/-- Every observed prefix stops inside the SAME cleanup with every protected
caller unchanged, or crosses the fully empty retirement boundary first. -/
theorem cleanup_prefix {n : Nat} {program : Program n}
    {start : OwnershipMir.Configuration (n + 1) (Op (n + 1))}
    (complete : Run Op.exec start ⟨.halt, emptyState n⟩) (frame : Frame n) (stack : List (Frame n))
    {after : Configuration n}
    (observed : Execution program ⟨.cleaning start.code, start.state, frame :: stack⟩ after) :
    (∃ current, Run Op.exec start current ∧ after = ⟨.cleaning current.code, current.state, frame :: stack⟩) ∨
      Execution program ⟨.body frame.next frame.cleanup, frame.state, stack⟩ after := by
  generalize finishEq : (OwnershipMir.Configuration.mk .halt (emptyState n)) = finish at complete
  induction complete generalizing after with
  | refl =>
    cases finishEq
    cases observed with
    | refl => exact Or.inl ⟨_, .refl _, rfl⟩
    | step head tail =>
      have same := head.deterministic (.retire (frame := frame) (stack := stack))
      cases same
      exact Or.inr tail
  | @step before middle finish head tail ih =>
    cases observed with
    | refl => exact Or.inl ⟨_, .refl _, rfl⟩
    | step first rest =>
      have same := first.deterministic (.clean head)
      cases same
      rcases ih rest finishEq with ⟨current, segment, equal⟩ | resumed
      · exact Or.inl ⟨current, .step head segment, equal⟩
      · exact Or.inr resumed

/-- The existing ordered-cleanup theorem is consumed at the actual call
boundary. No cleanup behavior or future result is an admission premise. -/
theorem Function.cleanup_prefix {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (admitted : (activationScope n).Admitted function.cleanupContext) {state : State (n + 1)}
    (typed : state.Typed signature function.cleanupContext) (frame : Frame n) (stack : List (Frame n))
    {after : Configuration n}
    (observed : Execution program ⟨.cleaning function.cleanup, state, frame :: stack⟩ after) :
    (∃ current events,
      OwnershipTrace ⟨function.cleanup, state⟩ current events ∧
      events.IsPrefix ((activationScope n).cleanupOrder function.cleanupContext) ∧
      after = ⟨.cleaning current.code, current.state, frame :: stack⟩) ∨
      Execution program ⟨.body frame.next frame.cleanup, frame.state, stack⟩ after := by
  rcases Calls.cleanup_prefix (function.cleanup_trace admitted typed).run frame stack observed with
    ⟨current, run, same⟩ | resumed
  · obtain ⟨events, trace⟩ := OwnershipTrace.of_run run
    exact Or.inl ⟨current, events, trace, trace.prefix (function.cleanup_trace admitted typed) rfl, same⟩
  · exact Or.inr resumed

theorem Function.cleanup_diverges_iff {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (admitted : (activationScope n).Admitted function.cleanupContext) {state : State (n + 1)}
    (typed : state.Typed signature function.cleanupContext) (frame : Frame n) (stack : List (Frame n)) :
    Diverges program ⟨.cleaning function.cleanup, state, frame :: stack⟩ ↔
      Diverges program ⟨.body frame.next frame.cleanup, frame.state, stack⟩ :=
  (function.cleanup_returns admitted typed frame stack).diverges_iff

/-- A boundary operation may change the top caller, never any deeper retained
caller. Interior frames may be pushed/popped without touching that suffix. -/
theorem Transition.retained_suffix {n : Nat} {program : Program n} {before after : Configuration n}
    (step : Transition program before after) (interiorFrames retained : List (Frame n))
    (partition : before.stack = interiorFrames ++ retained) (interior : interiorFrames ≠ []) :
    ∃ nextPrefix, after.stack = nextPrefix ++ retained := by
  cases interiorFrames with
  | nil => exact False.elim (interior rfl)
  | cons top rest =>
    cases step with
    | operation => exact ⟨top :: rest, partition⟩
    | enter => exact ⟨_ :: top :: rest, congrArg (_ :: ·) partition⟩
    | handoff =>
      rcases List.cons.inj partition with ⟨rfl, rfl⟩
      exact ⟨_ :: rest, rfl⟩
    | clean => exact ⟨top :: rest, partition⟩
    | retire =>
      rcases List.cons.inj partition with ⟨rfl, rfl⟩
      exact ⟨rest, rfl⟩

/-- Return installation changes no caller root outside the destination. The
ordinary place effect supplies the proof; there is no call-specific store walk. -/
theorem handoff_frame {n : Nat} (state : State (n + 1)) (frame : Frame n)
    {slots : Fin (n + 1) → Option Value}
    (installed : (Op.put frame.destination).exec ⟨frame.slots, state.temp⟩ = some ⟨slots, none⟩)
    (slot : Fin (n + 1)) (outside : slot ≠ frame.destination.root) : slots slot = frame.slots slot := by
  exact Op.exec_frame slot (by exact outside) installed

end OwnershipMir.Calls
