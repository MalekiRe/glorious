import Grounded.StorageOperations

/-! Addressed lexical bindings. Input residents are transient invocation data;
only storage identities are installed in the resulting binding map. -/
namespace Grounded

abbrev BindingMap := List (BindingId × StorageId)

structure BindingInput where
  name : BindingId
  slot : BindingType
  value : Value

structure BindingState where
  slot : BindingType
  initialization : Initialization

inductive BindingInputsTyped (program : Program) : List BindingInput → Prop where
  | nil : BindingInputsTyped program []
  | cons {input : BindingInput} {rest : List BindingInput}
      (resident : ValueHasType program input.value input.slot.type)
      (tail : BindingInputsTyped program rest)
      (fresh : input.name ∉ rest.map BindingInput.name) :
      BindingInputsTyped program (input :: rest)

def BindingInput.cell (input : BindingInput) (activation : ActivationId) : StorageCell :=
  ⟨activation, input.slot.type, .resident input.value⟩

def BindingInput.state (input : BindingInput) : BindingId × BindingState :=
  (input.name, ⟨input.slot, .present⟩)

/-- Allocation order is input order. There is no source-ID-to-address cast. -/
def allocateBindings (heap : RuntimeHeap StorageCell) (activation : ActivationId) :
    List BindingInput → BindingMap × RuntimeHeap StorageCell
  | [] => ([], heap)
  | input :: rest =>
      let first := heap.allocate (input.cell activation)
      let tail := allocateBindings first.2 activation rest
      ((input.name, first.1) :: tail.1, tail.2)

/-- Availability and declared type describe the actual cell, not a second
resident copy. Both lexical and storage identities are distinct in a scope. -/
inductive BindingMap.Typed (program : Program) (heap : RuntimeHeap StorageCell)
    (activation : ActivationId) : BindingMap → List (BindingId × BindingState) → Prop where
  | nil : BindingMap.Typed program heap activation [] []
  | cons {name : BindingId} {identity : StorageId} {cell : StorageCell} {state : BindingState}
      {bindings : BindingMap} {context : List (BindingId × BindingState)}
      (found : heap.read identity = some cell)
      (owner : cell.activation = activation) (declared : cell.type = state.slot.type)
      (resident : cell.Typed program state.initialization)
      (tail : BindingMap.Typed program heap activation bindings context)
      (freshName : name ∉ context.map Prod.fst)
      (freshStorage : identity ∉ bindings.map Prod.snd) :
      BindingMap.Typed program heap activation ((name, identity) :: bindings) ((name, state) :: context)

variable {program : Program} {heap after : RuntimeHeap StorageCell} {activation : ActivationId}
    {bindings : BindingMap} {context : List (BindingId × BindingState)}

theorem BindingMap.Typed.keys (typed : BindingMap.Typed program heap activation bindings context) :
    bindings.map Prod.fst = context.map Prod.fst := by
  induction typed with
  | nil => rfl
  | cons found owner declared resident tail freshName freshStorage ih => exact congrArg (List.cons _) ih

theorem BindingMap.Typed.addresses_distinct (typed : BindingMap.Typed program heap activation bindings context) :
    (bindings.map Prod.snd).Nodup := by
  induction typed with
  | nil => exact .nil
  | cons found owner declared resident tail freshName freshStorage ih => exact List.nodup_cons.mpr ⟨freshStorage, ih⟩

theorem BindingMap.Typed.live (typed : BindingMap.Typed program heap activation bindings context) :
    ∀ identity ∈ bindings.map Prod.snd, ∃ cell, heap.read identity = some cell := by
  induction typed with
  | nil => simp
  | cons found owner declared resident tail freshName freshStorage ih =>
    intro identity member
    cases member with
    | head => exact ⟨_, found⟩
    | tail _ member => exact ih identity member

/-- Exact cell framing transports realization; no post-state typing premise. -/
theorem BindingMap.Typed.frame (typed : BindingMap.Typed program heap activation bindings context)
    (unchanged : ∀ identity ∈ bindings.map Prod.snd, after.read identity = heap.read identity) :
    BindingMap.Typed program after activation bindings context := by
  induction typed with
  | nil => exact .nil
  | cons found owner declared resident tail freshName freshStorage ih =>
    exact .cons ((unchanged _ (by simp)).trans found) owner declared resident
      (ih (fun identity member => unchanged identity (List.mem_cons_of_mem _ member))) freshName freshStorage

theorem allocateBindings.old (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    (inputs : List BindingInput) {identity : StorageId} (old : identity.index < heap.next) :
    (allocateBindings heap activation inputs).2.read identity = heap.read identity := by
  induction inputs generalizing heap with
  | nil => rfl
  | cons input rest ih =>
    have different : identity ≠ (heap.allocate (input.cell activation)).1 := by
      intro same
      exact Nat.ne_of_lt old (congrArg StorageId.index same)
    exact (ih (heap.allocate (input.cell activation)).2 (Nat.lt_succ_of_lt old)).trans
      (heap.allocate_other _ _ different)

theorem allocateBindings.bounds (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    (inputs : List BindingInput) :
    ∀ identity ∈ (allocateBindings heap activation inputs).1.map Prod.snd, heap.next ≤ identity.index := by
  induction inputs generalizing heap with
  | nil => simp [allocateBindings]
  | cons input rest ih =>
    intro identity member
    cases member with
    | head => exact Nat.le_refl _
    | tail _ member => exact Nat.le_trans (Nat.le_succ _) (ih _ identity member)

theorem allocateBindings.keys (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    (inputs : List BindingInput) :
    (allocateBindings heap activation inputs).1.map Prod.fst = inputs.map BindingInput.name := by
  induction inputs generalizing heap with
  | nil => rfl
  | cons input rest ih => exact congrArg (List.cons input.name) (ih _)

theorem allocateBindings.typed {inputs : List BindingInput} (typed : BindingInputsTyped program inputs)
    (heap : RuntimeHeap StorageCell) (activation : ActivationId) :
    BindingMap.Typed program (allocateBindings heap activation inputs).2 activation
      (allocateBindings heap activation inputs).1 (inputs.map BindingInput.state) := by
  induction typed generalizing heap with
  | nil => exact .nil
  | @cons input rest resident tail fresh ih =>
    let first := heap.allocate (input.cell activation)
    have found : (allocateBindings first.2 activation rest).2.read first.1 = some (input.cell activation) :=
      (allocateBindings.old first.2 activation rest (Nat.lt_succ_self _)).trans (heap.allocate_read _)
    refine .cons found rfl rfl ⟨resident.finite, .resident resident⟩ (ih first.2) ?_ ?_
    · simpa [List.map_map, BindingInput.state, Function.comp_def] using fresh
    · intro member
      have lower := allocateBindings.bounds first.2 activation rest first.1 member
      change heap.next + 1 ≤ heap.next at lower
      omega

/-- Previously live bindings survive allocation, including shared retained
caller maps. No disjointness assumption about newly allocated addresses is needed. -/
theorem BindingMap.Typed.allocate (typed : BindingMap.Typed program heap activation bindings context)
    (owner : ActivationId) (inputs : List BindingInput) :
    BindingMap.Typed program (allocateBindings heap owner inputs).2 activation bindings context := by
  apply typed.frame
  intro identity member
  obtain ⟨cell, found⟩ := typed.live identity member
  exact allocateBindings.old heap owner inputs (heap.bounded identity cell found)

/-- Scope release retires identities, not lexical names or activation counters. -/
def releaseBindings (heap : RuntimeHeap StorageCell) (bindings : BindingMap) : Option (RuntimeHeap StorageCell) :=
  heap.retireMany (bindings.map Prod.snd)

theorem BindingMap.Typed.release (typed : BindingMap.Typed program heap activation bindings context) :
    ∃ after, releaseBindings heap bindings = some after ∧
      after.next = heap.next ∧
      (∀ identity ∈ bindings.map Prod.snd, after.Retired identity) ∧
      (∀ identity, identity ∉ bindings.map Prod.snd → after.read identity = heap.read identity) := by
  obtain ⟨after, released⟩ := heap.retireMany_exists _ typed.addresses_distinct typed.live
  exact ⟨after, released, RuntimeHeap.retireMany_next released,
    RuntimeHeap.retireMany_retired released, fun _ outside => RuntimeHeap.retireMany_outside released outside⟩

theorem BindingMap.Typed.lookup (typed : BindingMap.Typed program heap activation bindings context)
    {name : BindingId} {state : BindingState} (selected : lookup name context = some state) :
    ∃ identity cell, lookup name bindings = some identity ∧ heap.read identity = some cell ∧
      cell.activation = activation ∧ cell.type = state.slot.type ∧ cell.Typed program state.initialization ∧
      identity ∈ bindings.map Prod.snd := by
  induction typed with
  | nil => simp [Grounded.lookup] at selected
  | @cons key identity cell localState bindings context found owner declared resident tail freshName freshStorage ih =>
    simp only [Grounded.lookup] at selected ⊢
    split at selected
    next same =>
      cases selected
      exact ⟨identity, cell, by simp [same], found, owner, declared, resident, by simp⟩
    next different =>
      obtain ⟨address, actual, mapped, live, owned, typeEq, typedCell, member⟩ := ih selected
      exact ⟨address, actual, by simp [different, mapped], live, owned, typeEq, typedCell,
        List.mem_cons_of_mem _ member⟩

theorem replaceBinding.keys {α : Type} {name : BindingId} {value : α}
    {before after : List (BindingId × α)} (written : replaceBinding name value before = some after) :
    after.map Prod.fst = before.map Prod.fst := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at written
  | cons entry rest ih =>
    rcases entry with ⟨key, old⟩
    simp only [replaceBinding] at written
    split at written
    next same => cases written; rfl
    next different =>
      cases replaced : replaceBinding name value rest with
      | none => simp [replaced] at written
      | some tail =>
        simp [replaced] at written
        subst after
        exact congrArg (List.cons key) (ih replaced)

/-- Replacing one live cell updates exactly its checking state. Every other
binding retains the same cell and availability description. -/
theorem BindingMap.Typed.write (typed : BindingMap.Typed program heap activation bindings context)
    {name : BindingId} {state : BindingState} {identity : StorageId} {cell : StorageCell}
    {nextState : Initialization}
    (selected : Grounded.lookup name context = some state) (mapped : Grounded.lookup name bindings = some identity)
    (written : heap.write identity cell = some after)
    (owner : cell.activation = activation) (declared : cell.type = state.slot.type)
    (resident : cell.Typed program nextState) :
    ∃ nextContext, replaceBinding name { state with initialization := nextState } context = some nextContext ∧
      BindingMap.Typed program after activation bindings nextContext := by
  induction typed with
  | nil => simp [Grounded.lookup] at selected
  | @cons key address actual localState bindings context found owned typeEq cellTyped tail freshName freshStorage ih =>
    simp only [Grounded.lookup] at selected mapped
    split at selected
    next same =>
      subst key
      cases selected
      simp at mapped
      subst address
      refine ⟨(name, { state with initialization := nextState }) :: context, by simp [replaceBinding],
        .cons (RuntimeHeap.write_read written) owner declared resident ?_ freshName freshStorage⟩
      apply tail.frame
      intro other member
      apply RuntimeHeap.write_other written
      intro equal
      subst other
      exact freshStorage member
    next different =>
      simp only [if_neg different] at mapped
      obtain ⟨nextContext, replaced, nextTyped⟩ := ih selected mapped
      obtain ⟨target, old, targetMapped, _, _, _, _, targetMember⟩ := tail.lookup selected
      have targetEq := Option.some.inj (targetMapped.symm.trans mapped)
      subst target
      have apart : address ≠ identity := by
        intro equal
        exact freshStorage (equal.symm ▸ targetMember)
      refine ⟨(key, localState) :: nextContext, by simp [replaceBinding, Ne.symm different, replaced],
        .cons ((RuntimeHeap.write_other written apart).trans found) owned typeEq cellTyped nextTyped ?_ freshStorage⟩
      rw [replaceBinding.keys replaced]
      exact freshName

/-- Every allocated cell is well typed; unrelated heap cells are unchanged. -/
theorem allocateBindings.heap_typed {inputs : List BindingInput} (typed : BindingInputsTyped program inputs)
    (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    (store : heap.Typed (fun _ cell => cell.WellTyped program)) :
    (allocateBindings heap activation inputs).2.Typed (fun _ cell => cell.WellTyped program) := by
  induction typed generalizing heap with
  | nil => exact store
  | cons resident tail fresh ih =>
    exact ih _ (store.allocate _ ⟨.present, resident.finite, .resident resident⟩)

/-- Release preserves a retained caller map when ownership keeps its addresses
outside the released scope. Shared values are not silently copied into a frame. -/
theorem BindingMap.Typed.release_retained
    (typed : BindingMap.Typed program heap activation bindings context)
    {retained : BindingMap} {callerContext : List (BindingId × BindingState)} {caller : ActivationId}
    (callerTyped : BindingMap.Typed program heap caller retained callerContext)
    (apart : ∀ identity ∈ retained.map Prod.snd, identity ∉ bindings.map Prod.snd) :
    ∃ after, releaseBindings heap bindings = some after ∧
      BindingMap.Typed program after caller retained callerContext ∧
      after.next = heap.next ∧
      (∀ identity ∈ bindings.map Prod.snd, after.Retired identity) := by
  obtain ⟨after, released, next, retired, outside⟩ := typed.release
  exact ⟨after, released, callerTyped.frame (fun identity member => outside identity (apart identity member)),
    next, retired⟩

/-- Dynamic invocation entry consumes the activation supply, even for an empty
argument list. Lexical declaration IDs do not determine either dynamic identity. -/
def enterBindings (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) (inputs : List BindingInput) :
    ActivationId × ActivationSupply × BindingMap × RuntimeHeap StorageCell :=
  let activation := supply.allocate
  let allocated := allocateBindings heap activation.1 inputs
  (activation.1, activation.2, allocated.1, allocated.2)

theorem enterBindings.typed {inputs : List BindingInput} (typed : BindingInputsTyped program inputs)
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    BindingMap.Typed program (enterBindings heap supply inputs).2.2.2 (enterBindings heap supply inputs).1
      (enterBindings heap supply inputs).2.2.1 (inputs.map BindingInput.state) :=
  allocateBindings.typed typed heap supply.allocate.1

theorem enterBindings.fresh_activation (heap : RuntimeHeap StorageCell) (supply : ActivationSupply)
    (inputs : List BindingInput) :
    (enterBindings heap supply inputs).1.index = supply.next ∧
      (enterBindings heap supply inputs).2.1.next = supply.next + 1 := ⟨rfl, rfl⟩



theorem BindingMap.Typed.append {front back : BindingMap}
    {first rest : List (BindingId × BindingState)}
    (head : BindingMap.Typed program heap activation front first)
    (tail : BindingMap.Typed program heap activation back rest)
    (names : ((first ++ rest).map Prod.fst).Nodup)
    (addresses : ((front ++ back).map Prod.snd).Nodup) :
    BindingMap.Typed program heap activation (front ++ back) (first ++ rest) := by
  induction head with
  | nil => exact tail
  | cons found owner declared resident localTail freshName freshStorage ih =>
    have nameParts := List.nodup_cons.mp names
    have addressParts := List.nodup_cons.mp addresses
    exact .cons found owner declared resident (ih nameParts.2 addressParts.2) nameParts.1 addressParts.1

theorem BindingMap.Typed.allocate_apart (current : BindingMap.Typed program heap activation bindings context)
    (owner : ActivationId) (inputs : List BindingInput) :
    ∀ newAddress ∈ (allocateBindings heap owner inputs).1.map Prod.snd,
      ∀ oldAddress ∈ bindings.map Prod.snd, newAddress ≠ oldAddress := by
  intro newAddress newMember oldAddress oldMember same
  obtain ⟨cell, found⟩ := current.live oldAddress oldMember
  have lower := allocateBindings.bounds heap owner inputs newAddress newMember
  have upper := heap.bounded oldAddress cell found
  rw [same] at lower
  omega


/-- Scope extension consumes pre-state lexical freshness. Storage separation is
derived from allocation bounds and existing liveness, never assumed. -/
theorem allocateBindings.extend {inputs : List BindingInput} (inputsTyped : BindingInputsTyped program inputs)
    (current : BindingMap.Typed program heap activation bindings context)
    (fresh : (inputs.map BindingInput.name ++ context.map Prod.fst).Nodup) :
    BindingMap.Typed program (allocateBindings heap activation inputs).2 activation
      ((allocateBindings heap activation inputs).1 ++ bindings)
      (inputs.map BindingInput.state ++ context) := by
  have allocated := allocateBindings.typed inputsTyped heap activation
  have retained := current.allocate activation inputs
  apply allocated.append retained
  · simpa only [List.map_append, List.map_map, BindingInput.state, Function.comp_def] using fresh
  · rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨allocated.addresses_distinct, current.addresses_distinct, ?_⟩
    exact current.allocate_apart activation inputs


theorem BindingMap.Typed.take (typed : BindingMap.Typed program heap activation bindings context) (count : Nat) :
    BindingMap.Typed program heap activation (bindings.take count) (context.take count) := by
  induction count generalizing bindings context with
  | zero => exact .nil
  | succ count ih =>
    cases typed with
    | nil => exact .nil
    | cons found owner declared resident tail freshName freshStorage =>
      refine .cons found owner declared resident (ih tail) ?_ ?_
      · intro member
        obtain ⟨entry, included, equal⟩ := List.mem_map.mp member
        exact freshName (List.mem_map.mpr ⟨entry, List.mem_of_mem_take included, equal⟩)
      · intro member
        obtain ⟨entry, included, equal⟩ := List.mem_map.mp member
        exact freshStorage (List.mem_map.mpr ⟨entry, List.mem_of_mem_take included, equal⟩)

theorem BindingMap.Typed.drop (typed : BindingMap.Typed program heap activation bindings context) (count : Nat) :
    BindingMap.Typed program heap activation (bindings.drop count) (context.drop count) := by
  induction count generalizing bindings context with
  | zero => exact typed
  | succ count ih =>
    cases typed with
    | nil => exact .nil
    | cons found owner declared resident tail freshName freshStorage => exact ih tail

/-- Scope exit releases exactly the leading local bindings. Separation from
the surviving outer bindings follows from current ownership, not a release-success premise. -/
theorem BindingMap.Typed.exit_scope (typed : BindingMap.Typed program heap activation bindings context)
    (count : Nat) :
    ∃ after, releaseBindings heap (bindings.take count) = some after ∧
      BindingMap.Typed program after activation (bindings.drop count) (context.drop count) ∧
      after.next = heap.next ∧
      (∀ identity ∈ (bindings.take count).map Prod.snd, after.Retired identity) := by
  apply (typed.take count).release_retained (typed.drop count)
  intro identity retained released
  have distinct := typed.addresses_distinct
  rw [← List.take_append_drop count bindings, List.map_append] at distinct
  have apart := (List.nodup_append.mp distinct).2.2
  exact apart identity released identity retained rfl


/-- Pair runtime arguments with the already-resolved declared slots. Mismatched
arity is rejected rather than truncated by a zip. -/
def prepareBindings : List (BindingId × BindingType) → List Value → Option (List BindingInput)
  | [], [] => some []
  | (name, slot) :: parameters, value :: values =>
      (prepareBindings parameters values).map (⟨name, slot, value⟩ :: ·)
  | _, _ => none

def initializedContext (parameters : List (BindingId × BindingType)) : List (BindingId × BindingState) :=
  parameters.map fun parameter => (parameter.1, ⟨parameter.2, .present⟩)

theorem prepareBindings.progress {parameters : List (BindingId × BindingType)} {values : List Value}
    (typed : ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type)))
    (distinct : (parameters.map Prod.fst).Nodup) :
    ∃ inputs, prepareBindings parameters values = some inputs ∧ BindingInputsTyped program inputs ∧
      inputs.map BindingInput.name = parameters.map Prod.fst ∧
      inputs.map BindingInput.state = initializedContext parameters := by
  induction parameters generalizing values with
  | nil => cases typed; exact ⟨[], rfl, .nil, rfl, rfl⟩
  | cons parameter parameters ih =>
    cases typed with
    | cons head tail =>
      have parts := List.nodup_cons.mp distinct
      obtain ⟨inputs, prepared, inputsTyped, names, states⟩ := ih tail parts.2
      refine ⟨⟨parameter.1, parameter.2, _⟩ :: inputs, ?_, .cons head inputsTyped ?_, ?_, ?_⟩
      · cases parameter; simp [prepareBindings, prepared]
      · rw [names]; exact parts.1
      · exact congrArg (List.cons parameter.1) names
      · exact congrArg (List.cons (parameter.1, ⟨parameter.2, .present⟩)) states

/-- Direct function entry uses the declaration's resolved slots and the common
invocation allocator. The entry result contains no checking certificate. -/
def enterFunction (heap : RuntimeHeap StorageCell) (supply : ActivationSupply)
    (declaration : FunctionDecl) (values : List Value) :
    Option (ActivationId × ActivationSupply × BindingMap × RuntimeHeap StorageCell) :=
  (prepareBindings declaration.parameters values).map (enterBindings heap supply)

theorem enterFunction.progress {declaration : FunctionDecl} {values : List Value}
    (arguments : ValuesHaveTypes program values (declaration.parameters.map (fun parameter => parameter.2.type)))
    (distinct : (declaration.parameters.map Prod.fst).Nodup)
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    ∃ entry, enterFunction heap supply declaration values = some entry ∧
      BindingMap.Typed program entry.2.2.2 entry.1 entry.2.2.1 (initializedContext declaration.parameters) ∧
      entry.1.index = supply.next ∧ entry.2.1.next = supply.next + 1 ∧
      (¬supply.Issued entry.1) ∧ entry.2.1.Issued entry.1 ∧
      (∀ previous, supply.Issued previous → entry.2.1.Issued previous ∧ previous ≠ entry.1) ∧
      (∀ caller callerContext owner, BindingMap.Typed program heap owner caller callerContext →
        BindingMap.Typed program entry.2.2.2 owner caller callerContext ∧
        ∀ identity ∈ entry.2.2.1.map Prod.snd, identity ∉ caller.map Prod.snd) := by
  obtain ⟨inputs, prepared, inputsTyped, _, states⟩ := prepareBindings.progress arguments distinct
  refine ⟨enterBindings heap supply inputs, by simp [enterFunction, prepared], ?_, rfl, rfl,
    supply.allocate_fresh, supply.allocate_issued, ?_, ?_⟩
  · rw [← states]; exact enterBindings.typed inputsTyped heap supply
  · intro previous issued
    exact ⟨ActivationSupply.allocate_preserves issued, ActivationSupply.allocate_distinct issued⟩
  · intro caller callerContext owner callerTyped
    exact ⟨callerTyped.allocate supply.allocate.1 inputs,
      fun identity member oldMember => callerTyped.allocate_apart supply.allocate.1 inputs identity member identity oldMember rfl⟩


end Grounded
