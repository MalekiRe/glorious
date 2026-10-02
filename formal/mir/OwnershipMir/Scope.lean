import OwnershipMir.Cleanup

namespace OwnershipMir

/-- Fixed-slot lexical ownership, in acquisition order. Protected results and
retained storage are outside this list. Calls derive the list from their
complete activation region; this module supplies local cleanup semantics. -/
structure Scope (n : Nat) where
  owners : List (Fin n)
  distinct : owners.Nodup

def clearSlots {n : Nat} {α : Type} (owners : List (Fin n)) (slots : Fin n → Option α) : Fin n → Option α :=
  fun i => if i ∈ owners then none else slots i

def clearContext {n : Nat} (owners : List (Fin n)) (context : Context n) : Context n :=
  ⟨clearSlots owners context.slots, none⟩

/-- Atomic boundary meaning, independent of the generated cleanup operations. -/
def Scope.exit {n : Nat} (scope : Scope n) (state : State n) : State n :=
  ⟨clearSlots scope.owners state.slots, none⟩

def Cleanable {n : Nat} (owners : List (Fin n)) (context : Context n) : Prop :=
  ∀ i ∈ owners, ∀ shape, context.slots i = some shape → shape.disposable

def Scope.Admitted {n : Nat} (scope : Scope n) (context : Context n) : Prop :=
  context.temp = none ∧ Cleanable scope.owners context

/-- This list is already newest-first. The public scope entry reverses exactly
once; each root's structural schedule is produced by cleanupTree. -/
def cleanupOwners {n : Nat} : List (Fin n) → Context n → List (Command n)
  | [], _ => []
  | owner :: rest, context =>
    (match context.slots owner with
      | none => []
      | some shape => cleanupTree owner [] shape) ++
      cleanupOwners rest ⟨update context.slots owner none, none⟩

def Scope.commands {n : Nat} (scope : Scope n) (context : Context n) : List (Command n) :=
  cleanupOwners scope.owners.reverse context

@[simp] theorem clearSlots_cons {n : Nat} {α : Type} (owners : List (Fin n)) (slots : Fin n → Option α) (i : Fin n) :
    clearSlots owners (update slots i none) = clearSlots (i :: owners) slots := by
  funext j
  by_cases member : j ∈ owners <;> by_cases same : j = i <;> simp [clearSlots, update, member, same]

@[simp] theorem clearSlots_reverse {n : Nat} {α : Type} (owners : List (Fin n)) (slots : Fin n → Option α) :
    clearSlots owners.reverse slots = clearSlots owners slots := by
  funext i
  simp [clearSlots]

theorem cleanupOwners_checked {n : Nat} (owners : List (Fin n)) (context : Context n)
    (empty : context.temp = none) (allowed : Cleanable owners context) :
    Code.Checked Command.Checked context (sequence (cleanupOwners owners context))
      (clearContext owners context) := by
  induction owners generalizing context with
  | nil =>
    have same : clearContext [] context = context := by
      have slots : clearSlots [] context.slots = context.slots := by funext i; simp [clearSlots]
      simp only [clearContext, slots]
      cases context
      simp_all
    rw [same]
    exact .halt
  | cons owner rest ih =>
    let next : Context n := ⟨update context.slots owner none, none⟩
    have head : Code.Checked Command.Checked context
        (sequence (match context.slots owner with | none => [] | some shape => cleanupTree owner [] shape)) next := by
      cases found : context.slots owner with
      | none =>
        have same : next = context := by
          dsimp [next]
          rw [← found, update_self]
          cases context
          simp_all
        rw [same]
        exact .halt
      | some shape =>
        simpa [clearFocused, TreeFrame.rebuild, TreeFrame.path, next] using
          cleanupTree_checked owner shape .hole context empty found (allowed owner (by simp) shape found)
    have tailAllowed : Cleanable rest next := by
      intro i member shape found
      by_cases same : i = owner
      · subst i
        simp [next] at found
      · exact allowed i (by simp [member]) shape (by simpa [next, update, same] using found)
    have tail := ih next rfl tailAllowed
    simpa [cleanupOwners, clearContext, next] using sequence_checked_append head tail

theorem Scope.checked {n : Nat} {scope : Scope n} {context : Context n} (admitted : scope.Admitted context) :
    Code.Checked Command.Checked context (sequence (scope.commands context)) (clearContext scope.owners context) := by
  have allowed : Cleanable scope.owners.reverse context := by
    intro i member
    exact admitted.2 i (by simpa using member)
  simpa [Scope.commands, clearContext] using cleanupOwners_checked scope.owners.reverse context admitted.1 allowed

def Command.DisposesIn {n : Nat} (owners : List (Fin n)) : Command n → Prop
  | .dispose place => place.root ∈ owners
  | _ => False

theorem cleanupTree_disposes {n : Nat} (root : Fin n) (path : List Direction) (shape : Shape) :
    ∀ command ∈ cleanupTree root path shape, command.DisposesIn [root] := by
  induction shape generalizing path with
  | hole layout =>
    simp only [cleanupTree]
    split <;> simp [Command.DisposesIn, disposeAt]
  | nil => simp [cleanupTree, Command.DisposesIn, disposeAt]
  | leaf kind => simp [cleanupTree, Command.DisposesIn, disposeAt]
  | pair left right leftIH rightIH =>
    intro command member
    simp only [cleanupTree, List.mem_append, List.mem_singleton] at member
    rcases member with first | second | rfl
    · exact rightIH _ _ first
    · exact leftIH _ _ second
    · simp [disposeAt, Command.DisposesIn]
  | wrap shell body ih =>
    intro command member
    simp only [cleanupTree, List.mem_append, List.mem_singleton] at member
    rcases member with first | rfl
    · exact ih _ _ first
    · simp [disposeAt, Command.DisposesIn]

theorem cleanupOwners_disposes {n : Nat} (owners : List (Fin n)) (context : Context n) :
    ∀ command ∈ cleanupOwners owners context, command.DisposesIn owners := by
  induction owners generalizing context with
  | nil => simp [cleanupOwners]
  | cons owner rest ih =>
    intro command member
    simp only [cleanupOwners, List.mem_append] at member
    rcases member with head | tail
    · cases found : context.slots owner with
      | none => simp [found] at head
      | some shape =>
        have located := cleanupTree_disposes owner [] shape command (by simpa [found] using head)
        cases command <;> simp_all [Command.DisposesIn]
    · have located := ih _ command tail
      cases command <;> simp_all [Command.DisposesIn]

theorem Command.dispose_frame {n : Nat} {place : Place n} {before after : State n}
    (executed : (Command.dispose place).exec before = some after) (slot : Fin n) (apart : slot ≠ place.root) :
    after.slots slot = before.slots slot := by
  cases empty : before.temp with
  | some value => simp [Command.exec, empty] at executed
  | none =>
    cases located : place.find before.slots with
    | none => simp [Command.exec, empty, located] at executed
    | some lens =>
      cases live : lens.selected <;> simp [Command.exec, empty, located, live] at executed
      cases executed
      simp [Place.write, update, apart]

/-- Exact retained values, not merely their classifications or owner counts. -/
theorem sequence_disposal_frame {n : Nat} (commands : List (Command n)) (owners : List (Fin n))
    (within : ∀ command ∈ commands, command.DisposesIn owners) {before after : State n}
    (run : Run Command.exec ⟨sequence commands, before⟩ ⟨.halt, after⟩)
    (slot : Fin n) (retained : slot ∉ owners) : after.slots slot = before.slots slot := by
  induction commands generalizing before with
  | nil => cases run with
    | refl => rfl
    | step head tail => cases head
  | cons command commands ih =>
    cases run with
    | step head tail =>
      cases head with
      | act executed =>
        have first := within command (by simp)
        have rest : ∀ c ∈ commands, c.DisposesIn owners := fun c member => within c (by simp [member])
        have last := ih rest tail
        cases command with
        | move mode source target => cases first
        | copy source target => cases first
        | dispose place =>
          have apart : slot ≠ place.root := by intro same; exact retained (same ▸ first)
          exact last.trans (Command.dispose_frame executed slot apart)

/-- Cleanup implements atomic scope exit, including physical disappearance of
all local roots and unchanged retained/result slots. Permission is wholly a
pre-state structural condition; termination and the final state are derived. -/
theorem Scope.exit_run {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state : State n} (typed : state.Typed signature context) :
    Run Op.exec ⟨lower (sequence (scope.commands context)), state⟩ ⟨.halt, scope.exit state⟩ ∧
      (scope.exit state).Typed signature (clearContext scope.owners context) ∧
      Conserves signature state (scope.exit state) := by
  obtain ⟨result, run, final, conserved⟩ := sequence_run (scope.commands context) (Scope.checked admitted) typed
  have within : ∀ command ∈ scope.commands context, command.DisposesIn scope.owners := by
    intro command member
    have located := cleanupOwners_disposes scope.owners.reverse context command member
    cases command with
    | move mode source target => cases located
    | copy source target => cases located
    | dispose place => exact List.mem_reverse.mp located
  have slots : result.slots = (scope.exit state).slots := by
    funext i
    by_cases owned : i ∈ scope.owners
    · have gone : result.slots i = none := by
        exact Option.map_eq_none_iff.mp (show (result.slots i).map (Value.kind signature) = none from
          by simpa [clearContext, clearSlots, owned] using final.1 i)
      simp [Scope.exit, clearSlots, owned, gone]
    · simpa [Scope.exit, clearSlots, owned] using sequence_disposal_frame _ _ within run i owned
  have empty : result.temp = none := Option.map_eq_none_iff.mp final.2
  have same : result = scope.exit state := by
    cases result
    simp_all [Scope.exit]
  subst result
  exact ⟨lower_run run, final, conserved⟩

/-- User code and lexical cleanup compose through the existing checker. This
is the actual general prefix safety theorem for the extended ownership slice. -/
theorem Scope.program_safety {n : Nat} {signature : Signature} {scope : Scope n}
    {before middle : Context n} {body : Code n (Command n)}
    (checked : Code.Checked Command.Checked before body middle) (admitted : scope.Admitted middle)
    {initial : State n} (typed : initial.Typed signature before) (unique : initial.Unique)
    {reached : Configuration n (Op n)}
    (run : Run Op.exec ⟨lower (body.append (sequence (scope.commands middle))), initial⟩ reached) :
    Safe signature Op.Checked (clearContext scope.owners middle) reached ∧ reached.state.Unique ∧
      Conserves signature initial reached.state ∧
      (reached.code = .halt ∨ ∃ next, Step Op.exec reached next) ∧
      reached.state.linearShells ≤ initial.linearShells ∧
      ∃ amount, ShellTrace ⟨lower (body.append (sequence (scope.commands middle))), initial⟩ reached amount ∧
        reached.state.shells + amount = initial.shells := by
  have program := checked.append (Scope.checked admitted)
  have safety := compiled_ownership_safety program typed unique run
  have start : Safe signature Op.Checked (clearContext scope.owners middle)
      ⟨lower (body.append (sequence (scope.commands middle))), initial⟩ := ⟨_, typed, lower_checked program⟩
  exact ⟨safety.1, safety.2.1, safety.2.2.1, safety.2.2.2, start.linear_shells_run run, start.shell_run run⟩

end OwnershipMir
