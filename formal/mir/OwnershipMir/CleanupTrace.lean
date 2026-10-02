import OwnershipMir.Framing

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
    (trace : OwnershipTrace before after events) : Run Op.exec before after := by
  induction trace with
  | refl => exact .refl _
  | step head tail ih => exact .step head ih

theorem OwnershipTrace.of_run {n : Nat} {before after : Configuration n (Op n)}
    (run : Run Op.exec before after) : ∃ events, OwnershipTrace before after events := by
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

theorem OwnershipTrace.terminal_unique {n : Nat} {before middle after : Configuration n (Op n)} {first last}
    (left : OwnershipTrace before middle first) (leftHalt : middle.code = .halt)
    (right : OwnershipTrace before after last) (rightHalt : after.code = .halt) : first = last := by
  induction left generalizing after last with
  | refl => exact (right.empty_of_halt leftHalt).symm
  | step head tail ih =>
    cases right with
    | refl => exact False.elim (head.not_halt rightHalt)
    | step first rest =>
      cases head.deterministic first
      exact congrArg (_ ++ ·) (ih leftHalt rest rightHalt)

theorem OwnershipTrace.prefix {n : Nat} {before middle after : Configuration n (Op n)} {first all}
    (observed : OwnershipTrace before middle first) (complete : OwnershipTrace before after all)
    (halted : after.code = .halt) : first.IsPrefix all := by
  induction observed generalizing after all with
  | refl => exact ⟨all, rfl⟩
  | step head tail ih =>
    cases complete with
    | refl => exact False.elim (head.not_halt halted)
    | step first rest =>
      cases head.deterministic first
      obtain ⟨suffix, equal⟩ := ih rest halted
      exact ⟨suffix, by simpa only [List.append_assoc] using congrArg (_ ++ ·) equal⟩

theorem Block.exec_trace {n : Nat} (ops : List (Op n)) {before after : State n}
    (executed : Block.exec Op.exec ops before = some after) (next : Code n (Op n)) :
    OwnershipTrace ⟨Block.emit ops next, before⟩ ⟨next, after⟩ (ops.map Op.event) := by
  induction ops generalizing before with
  | nil => cases Option.some.inj executed; exact .refl _
  | cons op rest ih =>
    obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp executed
    exact .step (.act head) (ih tail)

theorem commands_trace {n : Nat} (commands : List (Command n)) {before after : State n}
    (executed : Block.exec Command.exec commands before = some after) :
    OwnershipTrace ⟨lower (sequence commands), before⟩ ⟨.halt, after⟩
      (commands.flatMap fun command => command.block.map Op.event) := by
  induction commands generalizing before with
  | nil => cases Option.some.inj executed; exact .refl _
  | cons command rest ih =>
    obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp executed
    have first := Block.exec_trace command.block (by rwa [Command.exec_eq] at head) (lower (sequence rest))
    exact first.trans (ih tail)

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

/-- Ordering and endpoint are both derived from actual execution. -/
theorem Scope.exit_trace {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context) :
    OwnershipTrace ⟨lower (sequence (scope.commands context)), state⟩ ⟨.halt, scope.exit state⟩
      (scope.cleanupOrder context) := by
  obtain ⟨result, executed, _, _⟩ :=
    Block.checked_exec Command.Checked.sound (scope.commands context) (Scope.checked admitted) typed
  have trace := commands_trace (scope.commands context) executed
  have same := (Scope.exit_iff admitted typed).mp trace.run
  simpa [same, scope.commands_order] using trace

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
    (run : Run Op.exec ⟨lower (sequence (scope.commands context)), state⟩ reached) :
    Safe signature Op.Checked (clearContext scope.owners context) reached ∧ reached.state.Unique ∧
      Conserves signature state reached.state ∧
      (reached.code = .halt ∨ ∃ next, Step Op.exec reached next) ∧
      (∀ slot, slot ∉ scope.owners → reached.state.slots slot = state.slots slot) ∧
      ∃ events, OwnershipTrace ⟨lower (sequence (scope.commands context)), state⟩ reached events ∧
        events.IsPrefix (scope.cleanupOrder context) := by
  have safety := compiled_ownership_safety (Scope.checked admitted) typed unique run
  obtain ⟨events, observed⟩ := OwnershipTrace.of_run run
  exact ⟨safety.1, safety.2.1, safety.2.2.1, safety.2.2.2, scope.cleanup_frame context run,
    events, observed, Scope.cleanup_prefix_order admitted typed observed⟩

end OwnershipMir
