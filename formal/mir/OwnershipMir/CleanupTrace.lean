import OwnershipMir.Framing
import OwnershipMir.Trace

namespace OwnershipMir

/-- Independent structural order, not a projection of generated commands.
Nested holes have no resident to detach or release. A root hole still has an
occupied binding to retire. Pairs visit right then left before their storage. -/
def cleanupOrder {n : Nat} (root : Fin n) (path : List Direction) : Shape → List (OwnershipEvent n)
  | .hole layout => if path = [] then [.detach ⟨root, path, layout⟩, .release] else []
  | .nil => [.detach ⟨root, path, .nil⟩, .release]
  | .leaf kind => [.detach ⟨root, path, .atom kind⟩, .release]
  | .pair left right =>
    cleanupOrder root (path ++ [.right]) right ++
      (cleanupOrder root (path ++ [.left]) left ++
        [.detach ⟨root, path, .pair (left.layout id) (right.layout id)⟩, .release])
  | .wrap shell body =>
    cleanupOrder root (path ++ [.body]) body ++
      [.detach ⟨root, path, .wrap shell (body.layout id)⟩, .release]

def ownerOrder {n : Nat} (slots : Fin n → Option Shape) (owner : Fin n) : List (OwnershipEvent n) :=
  match slots owner with
  | none => []
  | some shape => cleanupOrder owner [] shape

/-- The specification reads the original occupancy once; it does not simulate
the generator's successive cleared contexts. Newest acquired root is first. -/
def Scope.cleanupOrder {n : Nat} (scope : Scope n) (context : Context n) : List (OwnershipEvent n) :=
  scope.owners.reverse.flatMap (ownerOrder context.slots)

theorem cleanupTree_order {n : Nat} (root : Fin n) (path : List Direction) (shape : Shape) :
    (cleanupTree root path shape).flatMap (fun command => command.block.map Op.event) = cleanupOrder root path shape := by
  induction shape generalizing path <;>
    simp_all [cleanupTree, cleanupOrder, disposeAt, Command.block, Op.event]
  split <;> rfl

private theorem flatMap_eq_on {α β : Type} (xs : List α) {f g : α → List β}
    (agree : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [agree x (by simp), ih (fun y member => agree y (by simp [member]))]

theorem cleanupOwners_order {n : Nat} (owners : List (Fin n)) (distinct : owners.Nodup) (context : Context n) :
    (cleanupOwners owners context).flatMap (fun command => command.block.map Op.event) =
      owners.flatMap (ownerOrder context.slots) := by
  induction owners generalizing context with
  | nil => rfl
  | cons owner rest ih =>
    obtain ⟨absent, nodup⟩ := List.nodup_cons.mp distinct
    have tail := ih nodup (Context.mk (update context.slots owner none) none)
    have unchanged : rest.flatMap (ownerOrder (update context.slots owner none)) =
        rest.flatMap (ownerOrder context.slots) := by
      apply flatMap_eq_on
      intro other member
      have apart : other ≠ owner := by intro same; subst other; exact absent member
      simp [ownerOrder, update, apart]
    simp only [cleanupOwners, List.flatMap_append, List.flatMap_cons]
    rw [tail, unchanged]
    cases found : context.slots owner <;> simp [ownerOrder, found, cleanupTree_order]

theorem Scope.commands_order {n : Nat} (scope : Scope n) (context : Context n) :
    (scope.commands context).flatMap (fun command => command.block.map Op.event) = scope.cleanupOrder context :=
  cleanupOwners_order scope.owners.reverse
    (List.pairwise_reverse.mpr (scope.distinct.imp (fun apart same => apart same.symm))) context

/-- Cleanup hands off to an arbitrary continuation; the continuation need not
terminate or even be admitted for the cleanup boundary theorem to hold. -/
theorem Scope.exit_trace_then {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context)
    (next : Code n (Op n)) :
    OwnershipTrace ⟨(lower (sequence (scope.commands context))).append next, state⟩
      ⟨next, scope.exit state⟩ (scope.cleanupOrder context) := by
  obtain ⟨result, executed, _, _⟩ :=
    Block.checked_exec Command.Checked.progress Command.Checked.executed (scope.commands context) (Scope.checked admitted) typed
  have trace := commands_trace (scope.commands context) executed next
  have same : result = scope.exit state := (Scope.exit_iff admitted typed).mp (lower_run (Block.exec_run _ executed .halt))
  rw [same, scope.commands_order] at trace
  exact trace

/-- Every finite observation is either a cleanup prefix with a residual path
to handoff, or the complete cleanup trace followed by continuation observations.
No property of the continuation is assumed. The alternatives need not be exclusive. -/
theorem Scope.cleanup_then_prefix {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context)
    (next : Code n (Op n)) {reached : Configuration n (Op n)} {events : List (OwnershipEvent n)}
    (observed : OwnershipTrace ⟨(lower (sequence (scope.commands context))).append next, state⟩ reached events) :
    (∃ rest, events ++ rest = scope.cleanupOrder context ∧
      OwnershipTrace reached ⟨next, scope.exit state⟩ rest) ∨
    (∃ tail, events = scope.cleanupOrder context ++ tail ∧
      OwnershipTrace ⟨next, scope.exit state⟩ reached tail) := by
  rcases observed.compare (Scope.exit_trace_then admitted typed next) with inside | ⟨tail, equal, trace⟩
  · exact Or.inl inside
  · exact Or.inr ⟨tail, equal.symm, trace⟩

/-- Normal return factors through completed cleanup, with an exact event split.
Continuation actions are not misclassified as part of the cleanup schedule. -/
theorem Scope.cleanup_then_return_iff {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state result : State n} (typed : state.Typed signature context)
    (next : Code n (Op n)) (events : List (OwnershipEvent n)) :
    OwnershipTrace ⟨(lower (sequence (scope.commands context))).append next, state⟩ ⟨.halt, result⟩ events ↔
      ∃ tail, events = scope.cleanupOrder context ++ tail ∧
        OwnershipTrace ⟨next, scope.exit state⟩ ⟨.halt, result⟩ tail := by
  constructor
  · intro observed
    rcases Scope.cleanup_then_prefix admitted typed next observed with ⟨rest, equal, residual⟩ | completed
    · have empty := residual.empty_of_halt rfl
      have boundary := residual.run.from_terminal (fun _ step => step.not_halt rfl)
      exact ⟨[], by simpa only [empty, List.append_nil] using equal,
        by rw [boundary]; exact .refl _⟩
    · exact completed
  · rintro ⟨tail, equal, continuation⟩
    rw [equal]
    exact (Scope.exit_trace_then admitted typed next).trans continuation

/-- Cleanup cannot introduce or conceal divergence in the continuation. -/
theorem Scope.cleanup_then_diverges_iff {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context)
    (next : Code n (Op n)) :
    Diverges (Step Op.exec) ⟨(lower (sequence (scope.commands context))).append next, state⟩ ↔
      Diverges (Step Op.exec) ⟨next, scope.exit state⟩ :=
  (Scope.exit_trace_then admitted typed next).run.diverges_iff Step.deterministic

/-- Safety composes with checking of the continuation at the cleared context.
Unlike cleanup itself, the continuation may modify previously retained slots. -/
theorem Scope.cleanup_then_safety {n : Nat} {signature : Signature} {scope : Scope n} {context final : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context)
    (unique : state.Unique) {next : Code n (Op n)}
    (checked : Code.Checked Op.Checked (clearContext scope.owners context) next final)
    {reached : Configuration n (Op n)}
    (run : Run (Step Op.exec) ⟨(lower (sequence (scope.commands context))).append next, state⟩ reached) :
    Safe signature Op.Checked final reached ∧ reached.state.Unique ∧ Conserves signature state reached.state ∧
      ∃ events, OwnershipTrace ⟨(lower (sequence (scope.commands context))).append next, state⟩ reached events ∧
        ((∃ rest, events ++ rest = scope.cleanupOrder context ∧ OwnershipTrace reached ⟨next, scope.exit state⟩ rest) ∨
         (∃ tail, events = scope.cleanupOrder context ++ tail ∧ OwnershipTrace ⟨next, scope.exit state⟩ reached tail)) := by
  have start : Safe signature Op.Checked final
      ⟨(lower (sequence (scope.commands context))).append next, state⟩ :=
    ⟨context, typed, (lower_checked (Scope.checked admitted)).append checked⟩
  have safety := ownership_safety start unique run
  obtain ⟨events, observed⟩ := OwnershipTrace.of_run run
  exact ⟨safety.1, safety.2.1, safety.2.2.1, events, observed,
    Scope.cleanup_then_prefix admitted typed next observed⟩

/-- Standalone cleanup is the halt-continuation instance. -/
theorem Scope.exit_trace {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context) :
    OwnershipTrace ⟨lower (sequence (scope.commands context)), state⟩ ⟨.halt, scope.exit state⟩
      (scope.cleanupOrder context) := by
  simpa only [Code.append_halt] using Scope.exit_trace_then admitted typed .halt

/-- Any observed prefix, including a pause after detach and before release,
follows the structural specification. It cannot reverse fields or roots. -/
theorem Scope.cleanup_prefix_order {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context)
    {reached : Configuration n (Op n)} {events : List (OwnershipEvent n)}
    (observed : OwnershipTrace ⟨lower (sequence (scope.commands context)), state⟩ reached events) :
    events.IsPrefix (scope.cleanupOrder context) :=
  observed.prefix (Scope.exit_trace admitted typed) rfl

theorem Scope.cleanup_trace_iff {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state result : State n} (typed : state.Typed signature context)
    (events : List (OwnershipEvent n)) :
    OwnershipTrace ⟨lower (sequence (scope.commands context)), state⟩ ⟨.halt, result⟩ events ↔
      result = scope.exit state ∧ events = scope.cleanupOrder context := by
  constructor
  · intro trace
    exact ⟨(Scope.exit_iff admitted typed).mp trace.run,
      trace.terminal_unique rfl (Scope.exit_trace admitted typed) rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact Scope.exit_trace admitted typed

/-- The public prefix contract attaches ordered observations to every real
run while retaining the existing preservation and retained-storage guarantees. -/
theorem Scope.cleanup_observed_safety {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context)
    (unique : state.Unique) {reached : Configuration n (Op n)}
    (run : Run (Step Op.exec) ⟨lower (sequence (scope.commands context)), state⟩ reached) :
    Safe signature Op.Checked (clearContext scope.owners context) reached ∧ reached.state.Unique ∧
      Conserves signature state reached.state ∧
      (reached.code = .halt ∨ ∃ next, Step Op.exec reached next) ∧
      (∀ slot, slot ∉ scope.owners → reached.state.slots slot = state.slots slot) ∧
      ∃ events, OwnershipTrace ⟨lower (sequence (scope.commands context)), state⟩ reached events ∧
        events.IsPrefix (scope.cleanupOrder context) := by
  obtain ⟨safe, distinct, conserved, events, trace, _⟩ := Scope.cleanup_then_safety admitted typed unique
    (Code.Checked.halt (rule := Op.Checked)) (by simpa only [Code.append_halt] using run)
  have observed : OwnershipTrace ⟨lower (sequence (scope.commands context)), state⟩ reached events :=
    by simpa only [Code.append_halt] using trace
  exact ⟨safe, distinct, conserved, safe.progress Op.Checked.progress, scope.cleanup_frame context run,
    events, observed, Scope.cleanup_prefix_order admitted typed observed⟩

end OwnershipMir
