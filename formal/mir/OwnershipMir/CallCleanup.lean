import OwnershipMir.CallControl

namespace OwnershipMir.Calls
variable {authority : Authority}

theorem Run.cleaning {n : Nat} {program : Program n}
    {before after : OwnershipMir.Configuration (n + 1) (Op (n + 1))}
    (run : Run (Step Op.exec) before after) (store : Store (n + 1) Atom) (active : Nat)
    (live : store.region active = some before.state.slots) (register : store.temp = before.state.temp)
    (stack : List (Frame n)) :
    Run (Transition program) ⟨.cleaning before.code, store, active, stack⟩
      ⟨.cleaning after.code, store.replace active after.state.slots after.state.temp, active, stack⟩ := by
  induction run generalizing store with
  | @refl start =>
    have same : store.replace active start.state.slots start.state.temp = store := by
      rw [← register]; exact Store.replace_self live
    rw [same]; exact .refl _
  | @step before middle after head tail ih =>
    have first : Transition program ⟨.cleaning before.code, store, active, stack⟩
        ⟨.cleaning middle.code, store.replace active middle.state.slots middle.state.temp, active, stack⟩ :=
      .clean live (by simpa [register] using head)
    have rest := ih (store.replace active middle.state.slots middle.state.temp)
      (Store.replace_same (Store.region_bound live) _ _) rfl
    simpa only [Store.replace_replace] using Run.step first rest

theorem activation_exit {n : Nat} (state : State (n + 1)) : (activationScope n).exit state = emptyState n := by
  have slots : clearSlots (activationScope n).owners state.slots = fun _ => none := by
    funext i
    exact if_pos (List.mem_finRange i)
  simp only [Scope.exit, slots, emptyState]

theorem Function.cleanup_trace {n : Nat} {signature : Signature} {function : Function n}
    (admitted : (activationScope n).Admitted authority function.cleanupContext) {state : State (n + 1)}
    (typed : state.Typed signature function.cleanupContext) :
    OwnershipTrace ⟨function.cleanup, state⟩ ⟨.halt, emptyState n⟩
      ((activationScope n).cleanupOrder function.cleanupContext) := by
  simpa only [Function.cleanup, activation_exit] using Scope.exit_trace admitted typed

theorem Function.cleanup_returns {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (admitted : (activationScope n).Admitted authority function.cleanupContext)
    (store : Store (n + 1) Atom) (active : Nat) {slots : Region (n + 1) Atom}
    (live : store.region active = some slots)
    (typed : (State.mk slots store.temp).Typed signature function.cleanupContext)
    (frame : Frame n) (stack : List (Frame n)) :
    Run (Transition program) ⟨.cleaning function.cleanup, store, active, frame :: stack⟩
      ⟨.body frame.next frame.cleanup, store.retire active, frame.region, stack⟩ := by
  have register : store.temp = none := Option.map_eq_none_iff.mp typed.2
  have cleaned := Run.cleaning (program := program) (function.cleanup_trace admitted typed).run store active live rfl (frame :: stack)
  have retired := Transition.retire (program := program) (store := store.replace active (fun _ => none) none)
    (frame := frame) (stack := stack) (Store.replace_same (Store.region_bound live) _ _) rfl
  have complete := cleaned.trans (.step retired (.refl _))
  simpa [emptyState, Store.replace, Store.retire, List.set_set, register] using complete

/-- The physical prefix is a prefix of the same local cleanup, or has crossed
empty retirement. Store identities and all exterior cells are retained. -/
theorem cleanup_prefix {n : Nat} {program : Program n}
    {start : OwnershipMir.Configuration (n + 1) (Op (n + 1))}
    (complete : Run (Step Op.exec) start ⟨.halt, emptyState n⟩)
    (store : Store (n + 1) Atom) (active : Nat)
    (live : store.region active = some start.state.slots) (register : store.temp = start.state.temp)
    (frame : Frame n) (stack : List (Frame n)) {after : Configuration n}
    (observed : Run (Transition program) ⟨.cleaning start.code, store, active, frame :: stack⟩ after) :
    (∃ current, Run (Step Op.exec) start current ∧
      after = ⟨.cleaning current.code, store.replace active current.state.slots current.state.temp, active, frame :: stack⟩) ∨
      Run (Transition program)
        ⟨.body frame.next frame.cleanup, {store.retire active with temp := none}, frame.region, stack⟩ after := by
  generalize finishEq : (OwnershipMir.Configuration.mk .halt (emptyState n)) = finish at complete
  induction complete generalizing store after with
  | refl =>
    cases finishEq
    cases observed with
    | refl =>
      refine Or.inl ⟨_, .refl _, ?_⟩
      rw [← register, Store.replace_self live]
    | step head tail =>
      have same := head.deterministic (.retire live register)
      cases same
      exact Or.inr (by simpa [Store.retire, register, emptyState] using tail)
  | @step before middle finish head tail ih =>
    cases observed with
    | refl =>
      refine Or.inl ⟨_, .refl _, ?_⟩
      rw [← register, Store.replace_self live]
    | step first rest =>
      have same := first.deterministic (.clean live (by simpa [register] using head))
      cases same
      rcases ih (store.replace active middle.state.slots middle.state.temp)
        (Store.replace_same (Store.region_bound live) _ _) rfl rest finishEq with ⟨current, segment, equal⟩ | resumed
      · exact Or.inl ⟨current, .step head segment, by simpa only [Store.replace_replace] using equal⟩
      · exact Or.inr (by simpa [Store.retire_replace] using resumed)

theorem Function.cleanup_prefix {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (admitted : (activationScope n).Admitted authority function.cleanupContext)
    (store : Store (n + 1) Atom) (active : Nat) {slots : Region (n + 1) Atom}
    (live : store.region active = some slots)
    (typed : (State.mk slots store.temp).Typed signature function.cleanupContext)
    (frame : Frame n) (stack : List (Frame n)) {after : Configuration n}
    (observed : Run (Transition program) ⟨.cleaning function.cleanup, store, active, frame :: stack⟩ after) :
    (∃ current events, OwnershipTrace ⟨function.cleanup, ⟨slots, store.temp⟩⟩ current events ∧
      events.IsPrefix ((activationScope n).cleanupOrder function.cleanupContext) ∧
      after = ⟨.cleaning current.code, store.replace active current.state.slots current.state.temp, active, frame :: stack⟩) ∨
      Run (Transition program) ⟨.body frame.next frame.cleanup, store.retire active, frame.region, stack⟩ after := by
  have register : store.temp = none := Option.map_eq_none_iff.mp typed.2
  rcases Calls.cleanup_prefix (function.cleanup_trace admitted typed).run store active live rfl frame stack observed with
    ⟨current, run, same⟩ | resumed
  · obtain ⟨events, trace⟩ := OwnershipTrace.of_run run
    exact Or.inl ⟨current, events, trace, trace.prefix (function.cleanup_trace admitted typed) rfl, same⟩
  · exact Or.inr (by simpa [Store.retire, register] using resumed)

theorem Function.cleanup_diverges_iff {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (admitted : (activationScope n).Admitted authority function.cleanupContext)
    (store : Store (n + 1) Atom) (active : Nat) {slots : Region (n + 1) Atom}
    (live : store.region active = some slots)
    (typed : (State.mk slots store.temp).Typed signature function.cleanupContext) (frame : Frame n) (stack : List (Frame n)) :
    Diverges (Transition program) ⟨.cleaning function.cleanup, store, active, frame :: stack⟩ ↔
      Diverges (Transition program) ⟨.body frame.next frame.cleanup, store.retire active, frame.region, stack⟩ :=
  (function.cleanup_returns admitted store active live typed frame stack).diverges_iff Transition.deterministic

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
    | handoff => exact ⟨top :: rest, partition⟩
    | clean => exact ⟨top :: rest, partition⟩
    | retire =>
      rcases List.cons.inj partition with ⟨rfl, rfl⟩
      exact ⟨rest, rfl⟩

theorem handoff_frame {n : Nat} {caller slots : Region (n + 1) Atom} {temp : Cell Atom} (frame : Frame n)
    (installed : (Op.put frame.destination).exec ⟨caller, temp⟩ = some ⟨slots, none⟩)
    (slot : Fin (n + 1)) (outside : slot ≠ frame.destination.root) : slots slot = caller slot := by
  exact Op.exec_frame slot (by exact outside) installed

/-- The actual return-to-caller retirement preserves all loan guarantees and
permissions from the before-state invariant. No escape or post-state premise
is needed once the retiring storage is empty. -/
theorem retirement_borrow_safe {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {active : Nat} (frame : Frame n) (stack : List (Frame n))
    (valid : store.BorrowInvariant signature) (empty : store.region active = some (fun _ => none))
    (register : store.temp = none) :
    ∃ after, Transition program ⟨.cleaning .halt, store, active, frame :: stack⟩ after ∧
      after.store.BorrowInvariant signature ∧ after.active = frame.region ∧ after.stack = stack ∧
      (∀ via mode address, after.store.Permitted via mode address ↔ store.Permitted via mode address) :=
  ⟨⟨.body frame.next frame.cleanup, store.retire active, frame.region, stack⟩,
    .retire empty register, valid.retire_empty empty, rfl, rfl, store.retire_empty_permissions empty⟩


/-- Releasing a physical handle executes the existing cleanup instruction.
The referent must be initialized before ending the handle; remaining aliases
and descendants determine which loans stay active. -/
theorem release_handle_borrow_safe {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {active identity : Nat} {mode : BorrowMode} {target : Layout}
    {slots : Region (n + 1) Atom} (next : Code (n + 1) (Op (n + 1))) (stack : List (Frame n))
    (valid : store.BorrowInvariant signature) (live : store.region active = some slots)
    (register : store.temp = some (.leaf (.reference identity mode target)))
    (ready : store.LoanReady identity) :
    ∃ after loan lens referent,
      Transition program ⟨.cleaning (.act .drop next), store, active, stack⟩ after ∧
      after.store.BorrowInvariant signature ∧
      store.loans[identity]? = some loan ∧ store.find loan.referent loan.target = some lens ∧
      lens.selected = some referent ∧ referent.ready ∧
      after.store = {store with temp := none} ∧
      (∀ origin, after.store.Active origin ↔
        ∃ handle mode target region slots root value, store.region region = some slots ∧
          slots root = some value ∧ value.Contains (.reference handle mode target) ∧ store.Ancestor origin handle) ∧
      (∀ requested address,
        (∀ origin loan handle mode target region slots root value,
          store.loans[origin]? = some loan → store.region region = some slots → slots root = some value →
          value.Contains (.reference handle mode target) → store.Ancestor origin handle →
          address.Overlaps loan.referent → requested = .shared ∧ loan.mode = .shared) →
        after.store.Permitted none requested address) := by
  obtain ⟨loan, lens, referent, found, focused, selected, initialized⟩ := ready
  have cleared : store.replace active slots none = {store with temp := none} := by
    have same := congrArg (fun result : Store (n + 1) Atom => {result with temp := none}) (Store.replace_self live)
    simpa only [Store.replace] using same
  refine ⟨⟨.cleaning next, {store with temp := none}, active, stack⟩,
    loan, lens, referent, ?_, valid.clearTemp, found, focused, selected, initialized, rfl,
    store.clearTemp_active_iff, fun requested address lastUse => Store.clearTemp_owner_permission requested address lastUse⟩
  rw [← cleared]
  exact .clean live (.act (op := Op.drop) (after := State.mk slots none) (by simp [Op.exec, register]))


end OwnershipMir.Calls
