import Grounded.BindingStorage

/-! Resolved lexical accesses use the same addressed cells and path operations
as allocation and scope retirement. Language permission is checked above here. -/
namespace Grounded

def BindingMap.read (bindings : BindingMap) (program : Program) (heap : RuntimeHeap StorageCell)
    (place : Place) : Option Value := do
  let identity ← lookup place.root bindings
  let cell ← heap.read identity
  let resident ← cell.resident.selectFields program cell.type place.fields
  resident.read

def BindingMap.take (bindings : BindingMap) (program : Program) (heap : RuntimeHeap StorageCell)
    (place : Place) : Option (Value × RuntimeHeap StorageCell) :=
  (lookup place.root bindings).bind fun identity => takeStorage program heap identity place.fields

def BindingMap.restore (bindings : BindingMap) (program : Program) (heap : RuntimeHeap StorageCell)
    (place : Place) (value : Value) : Option (RuntimeHeap StorageCell) :=
  (lookup place.root bindings).bind fun identity => restoreStorage program heap identity place.fields value

variable {program : Program} {home : Module} {heap : RuntimeHeap StorageCell} {activation : ActivationId}
    {bindings : BindingMap} {context : List (BindingId × BindingState)}
    {place : Place} {state : BindingState} {type : Ty}

/-- Exact retained cells preserve every projected read, including unsuccessful
reads. This is independent of the selected path or its source typing. -/
theorem BindingMap.read.frame {after : RuntimeHeap StorageCell}
    (unchanged : ∀ identity ∈ bindings.map Prod.snd, after.read identity = heap.read identity) :
    bindings.read program after place = bindings.read program heap place := by
  unfold BindingMap.read
  cases mapped : lookup place.root bindings with
  | none => rfl
  | some identity =>
    have member : identity ∈ bindings.map Prod.snd :=
      List.mem_map.mpr ⟨(place.root, identity), lookup.mem mapped, rfl⟩
    change (after.read identity).bind _ = (heap.read identity).bind _
    rw [unchanged identity member]

theorem BindingMap.read.progress (typed : BindingMap.Typed program heap activation bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {selectedState : Initialization}
    (selected : state.initialization.selectFields program state.slot.type place.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value, bindings.read program heap place = some value ∧ ValueHasType program value type := by
  obtain ⟨identity, cell, mapped, found, _, declared, resident, _⟩ := typed.lookup resolved
  have path : PathType program home cell.type place.fields type := by simpa only [declared] using checked
  obtain ⟨selectedResident, actualState, stateFound, partialFound, partialTyped⟩ := path.select_partial resident.2
  rw [declared, selected] at stateFound
  cases stateFound
  obtain ⟨value, read, valueTyped⟩ := partialTyped.read ready
  exact ⟨value, by simp [BindingMap.read, mapped, found, partialFound, read], valueTyped⟩

/-- A move changes the checking state and the actual resident together. The
same binding map survives; every other storage identity is framed. -/
theorem BindingMap.take.progress (typed : BindingMap.Typed program heap activation bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {selectedState : Initialization}
    (selected : state.initialization.selectFields program state.slot.type place.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ identity value after nextState nextContext,
      lookup place.root bindings = some identity ∧
      state.initialization.writeFields program state.slot.type place.fields .absent = some nextState ∧
      replaceBinding place.root { state with initialization := nextState } context = some nextContext ∧
      bindings.take program heap place = some (value, after) ∧
      ValueHasType program value type ∧
      BindingMap.Typed program after activation bindings nextContext ∧
      bindings.take program after place = none ∧ after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program heap caller.activation caller.bindings states →
        caller.activation ≠ activation → BindingMap.Typed program after caller.activation caller.bindings states ∧
          (∀ identity ∈ caller.bindings.map Prod.snd, after.read identity = heap.read identity)) := by
  obtain ⟨identity, cell, mapped, found, owner, declared, resident, _⟩ := typed.lookup resolved
  have path : PathType program home cell.type place.fields type := by simpa only [declared] using checked
  have selection : state.initialization.selectFields program cell.type place.fields = some selectedState := by
    simpa only [declared] using selected
  obtain ⟨value, after, updated, nextState, stateWritten, taken, valueTyped, written, updatedTyped,
    _, noRetake, next, framed⟩ := takeStorage.progress found resident path selection ready
  obtain ⟨nextContext, replaced, afterTyped⟩ := typed.write resolved mapped written owner declared updatedTyped
  exact ⟨identity, value, after, nextState, nextContext, mapped,
    by simpa only [declared] using stateWritten, replaced,
    by simp [BindingMap.take, mapped, taken], valueTyped, afterTyped,
    by simp [BindingMap.take, mapped, noRetake], next, framed,
    fun _ _ callerTyped different => callerTyped.frame_other_activation found
      (by simpa only [owner] using different) framed⟩

/-- Restoration updates a live slot, including a partially absent aggregate;
it does not allocate a replacement identity or revive retired storage. -/
theorem BindingMap.restore.progress (typed : BindingMap.Typed program heap activation bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {value : Value} (valueTyped : ValueHasType program value type) :
    ∃ identity after nextState nextContext,
      lookup place.root bindings = some identity ∧
      state.initialization.writeFields program state.slot.type place.fields .present = some nextState ∧
      replaceBinding place.root { state with initialization := nextState } context = some nextContext ∧
      bindings.restore program heap place value = some after ∧
      BindingMap.Typed program after activation bindings nextContext ∧
      bindings.read program after place = some value ∧ after.next = heap.next ∧
      (∀ other, other ≠ identity → after.read other = heap.read other) ∧
      (state.initialization.Ready → nextState.Ready) ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program heap caller.activation caller.bindings states →
        caller.activation ≠ activation → BindingMap.Typed program after caller.activation caller.bindings states ∧
          (∀ identity ∈ caller.bindings.map Prod.snd, after.read identity = heap.read identity)) := by
  obtain ⟨identity, cell, mapped, found, owner, declared, resident, _⟩ := typed.lookup resolved
  have path : PathType program home cell.type place.fields type := by simpa only [declared] using checked
  obtain ⟨after, updated, nextState, stateWritten, restored, written, updatedTyped,
    updatedFound, readback, next, framed⟩ := restoreStorage.progress found resident path valueTyped
  obtain ⟨nextContext, replaced, afterTyped⟩ := typed.write resolved mapped written owner declared updatedTyped
  exact ⟨identity, after, nextState, nextContext, mapped,
    by simpa only [declared] using stateWritten, replaced,
    by simp [BindingMap.restore, mapped, restored], afterTyped,
    by simp [BindingMap.read, mapped, updatedFound, readback, PartialValue.read], next, framed,
    (fun ready => Initialization.write_ready ready .present stateWritten),
    fun _ _ callerTyped different => callerTyped.frame_other_activation found
      (by simpa only [owner] using different) framed⟩

def AddressedEnvironment.read (current : AddressedEnvironment) (program : Program) (place : Place) : Option Value :=
  current.bindings.read program current.heap place

def AddressedEnvironment.take (current : AddressedEnvironment) (program : Program) (place : Place) :
    Option (Value × AddressedEnvironment) :=
  (current.bindings.take program current.heap place).map fun result =>
    (result.1, { current with heap := result.2 })

def AddressedEnvironment.write (current : AddressedEnvironment) (program : Program) (place : Place) (value : Value) :
    Option AddressedEnvironment :=
  (current.bindings.restore program current.heap place value).map fun heap => { current with heap := heap }

theorem AddressedEnvironment.read.progress {current : AddressedEnvironment}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {selectedState : Initialization}
    (selected : state.initialization.selectFields program state.slot.type place.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value, current.read program place = some value ∧ ValueHasType program value type :=
  BindingMap.read.progress typed resolved checked selected ready

theorem AddressedEnvironment.take.progress {current : AddressedEnvironment}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {selectedState : Initialization}
    (selected : state.initialization.selectFields program state.slot.type place.fields = some selectedState)
    (ready : selectedState.Ready) :
    ∃ value after nextState nextContext,
      current.take program place = some (value, after) ∧ ValueHasType program value type ∧
      state.initialization.writeFields program state.slot.type place.fields .absent = some nextState ∧
      replaceBinding place.root { state with initialization := nextState } context = some nextContext ∧
      BindingMap.Typed program after.heap after.activation after.bindings nextContext ∧
      after.take program place = none ∧ after.scope = current.scope ∧ after.supply = current.supply ∧
      after.heap.next = current.heap.next ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program current.heap caller.activation caller.bindings states →
        caller.activation ≠ current.activation → BindingMap.Typed program after.heap caller.activation caller.bindings states ∧
          (∀ identity ∈ caller.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity)) := by
  obtain ⟨identity, value, heap, nextState, nextContext, _, stateWritten, replaced,
    taken, resident, afterTyped, noRetake, next, _, retained⟩ :=
    BindingMap.take.progress typed resolved checked selected ready
  exact ⟨value, { current with heap := heap }, nextState, nextContext,
    by simp [AddressedEnvironment.take, taken], resident, stateWritten, replaced, afterTyped,
    by simp [AddressedEnvironment.take, noRetake], rfl, rfl, next, retained⟩

theorem AddressedEnvironment.write.progress {current : AddressedEnvironment}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings context)
    (resolved : lookup place.root context = some state)
    (checked : PathType program home state.slot.type place.fields type)
    {value : Value} (resident : ValueHasType program value type) :
    ∃ after nextState nextContext,
      current.write program place value = some after ∧
      state.initialization.writeFields program state.slot.type place.fields .present = some nextState ∧
      replaceBinding place.root { state with initialization := nextState } context = some nextContext ∧
      BindingMap.Typed program after.heap after.activation after.bindings nextContext ∧
      after.read program place = some value ∧ after.scope = current.scope ∧ after.supply = current.supply ∧
      after.heap.next = current.heap.next ∧ (state.initialization.Ready → nextState.Ready) ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program current.heap caller.activation caller.bindings states →
        caller.activation ≠ current.activation → BindingMap.Typed program after.heap caller.activation caller.bindings states ∧
          (∀ identity ∈ caller.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity)) := by
  obtain ⟨identity, heap, nextState, nextContext, _, stateWritten, replaced,
    written, afterTyped, readback, next, _, initialized, retained⟩ :=
    BindingMap.restore.progress typed resolved checked resident
  exact ⟨{ current with heap := heap }, nextState, nextContext,
    by simp [AddressedEnvironment.write, written], stateWritten, replaced, afterTyped,
    readback, rfl, rfl, next, initialized, retained⟩


/-- The initialized source fragment is realized by the authoritative partial
cell typing. Readiness is a property of its masks, not another resident store. -/
def AddressedScope.Realizes (scope : AddressedScope) (program : Program)
    (heap : RuntimeHeap StorageCell) (context : List (BindingId × BindingType)) : Prop :=
  ∃ states, BindingMap.Typed program heap scope.activation scope.bindings states ∧
    (states.map fun entry => (entry.1, entry.2.slot)) = context ∧
    (∀ entry ∈ states, entry.2.initialization.Ready)

def AddressedEnvironment.Realizes (current : AddressedEnvironment) (program : Program)
    (context : List (BindingId × BindingType)) : Prop :=
  current.scope.Realizes program current.heap context ∧ current.supply.Issued current.activation

theorem AddressedEnvironment.Realizes.initialized {current : AddressedEnvironment}
    {context : List (BindingId × BindingType)}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings (initializedContext context))
    (issued : current.supply.Issued current.activation) : current.Realizes program context := by
  refine ⟨⟨initializedContext context, typed, ?_, ?_⟩, issued⟩
  · simp [initializedContext, List.map_map, Function.comp_def]
  · intro entry member
    obtain ⟨parameter, _, same⟩ := List.mem_map.mp member
    subst entry
    exact .present

theorem AddressedEnvironment.Realizes.read {current : AddressedEnvironment}
    {context : List (BindingId × BindingType)} {slot : BindingType}
    (realized : current.Realizes program context)
    (resolved : lookup place.root context = some slot)
    (checked : PathType program home slot.type place.fields type) :
    ∃ value, current.read program place = some value ∧ ValueHasType program value type := by
  obtain ⟨⟨states, typed, slots, ready⟩, _⟩ := realized
  rw [← slots, lookup.map] at resolved
  obtain ⟨state, selected, sameSlot⟩ := Option.map_eq_some_iff.mp resolved
  have rootReady := ready (place.root, state) (lookup.mem selected)
  have checkedState : PathType program home state.slot.type place.fields type := by
    rw [sameSlot]; exact checked
  obtain ⟨identity, cell, _, _, _, declared, resident, _⟩ := typed.lookup selected
  have checkedCell : PathType program home cell.type place.fields type := by
    simpa only [declared] using checkedState
  obtain ⟨part, selectedState, stateFound, _, _⟩ := checkedCell.select_partial resident.2
  rw [declared] at stateFound
  exact AddressedEnvironment.read.progress typed selected checkedState stateFound
    (Initialization.select_ready rootReady stateFound)


theorem BindingMap.restore.cell_other {after : RuntimeHeap StorageCell} {name : BindingId} {other : StorageId} {value : Value}
    (distinct : (bindings.map Prod.snd).Nodup)
    (written : bindings.restore program heap place value = some after)
    (otherMapped : lookup name bindings = some other) (different : name ≠ place.root) :
    after.read other = heap.read other := by
  simp only [BindingMap.restore, restoreStorage, Option.bind_eq_some_iff] at written
  obtain ⟨identity, mapped, cell, _, updated, _, stored⟩ := written
  apply RuntimeHeap.write_other stored
  intro same
  subst other
  exact different (lookup.unique_key distinct otherMapped mapped)

theorem BindingMap.restore.read_other {after : RuntimeHeap StorageCell} {other : Place} {value : Value}
    (distinct : (bindings.map Prod.snd).Nodup)
    (written : bindings.restore program heap place value = some after)
    (different : other.root ≠ place.root) :
    bindings.read program after other = bindings.read program heap other := by
  cases otherMapped : lookup other.root bindings with
  | none => simp [BindingMap.read, otherMapped]
  | some identity =>
    simp [BindingMap.read, otherMapped, BindingMap.restore.cell_other distinct written otherMapped different]

/-- Frame exact immutable cells. Every source read is a consequence, not a
separately maintained value snapshot. -/
def AddressedEnvironment.Frames (context : List (BindingId × BindingType))
    (before after : AddressedEnvironment) : Prop :=
  after.scope = before.scope ∧
    ∀ (name : BindingId) (slot : BindingType) (identity : StorageId),
      lookup name context = some slot → slot.mutable = false → lookup name before.bindings = some identity →
      after.heap.read identity = before.heap.read identity

theorem AddressedEnvironment.Frames.refl (context : List (BindingId × BindingType)) (current : AddressedEnvironment) :
    Frames context current current := ⟨rfl, fun _ _ _ _ _ _ => rfl⟩

theorem AddressedEnvironment.Frames.trans {context : List (BindingId × BindingType)}
    {before middle after : AddressedEnvironment} (first : Frames context before middle)
    (second : Frames context middle after) : Frames context before after := by
  refine ⟨second.1.trans first.1, ?_⟩
  intro name slot identity selected immutable mapped
  have maps := congrArg AddressedScope.bindings first.1
  simp only [AddressedEnvironment.scope] at maps
  exact (second.2 name slot identity selected immutable (by rw [maps]; exact mapped)).trans
    (first.2 name slot identity selected immutable mapped)

theorem AddressedEnvironment.Frames.read {context : List (BindingId × BindingType)}
    {before after : AddressedEnvironment} (framed : Frames context before after)
    {place : Place} {slot : BindingType} (selected : lookup place.root context = some slot)
    (immutable : slot.mutable = false) : after.read program place = before.read program place := by
  have maps := congrArg AddressedScope.bindings framed.1
  simp only [AddressedEnvironment.scope] at maps
  simp only [AddressedEnvironment.read]
  rw [maps]
  unfold BindingMap.read
  cases mapped : lookup place.root before.bindings with
  | none => rfl
  | some identity =>
    change (after.heap.read identity).bind _ = (before.heap.read identity).bind _
    rw [framed.2 place.root slot identity selected immutable mapped]

theorem AddressedEnvironment.write.frame {current after : AddressedEnvironment}
    {context : List (BindingId × BindingType)} {slot : BindingType} {value : Value}
    (realized : current.Realizes program context) (resolved : lookup place.root context = some slot)
    (writable : slot.mutable = true) (written : current.write program place value = some after) :
    AddressedEnvironment.Frames context current after := by
  obtain ⟨⟨states, typed, _, _⟩, _⟩ := realized
  obtain ⟨heap, restored, same⟩ := Option.map_eq_some_iff.mp written
  subst after
  refine ⟨rfl, ?_⟩
  intro other otherSlot identity selected immutable mapped
  apply BindingMap.restore.cell_other typed.addresses_distinct restored mapped
  intro sameRoot
  rw [sameRoot, resolved] at selected
  cases Option.some.inj selected
  simp_all


theorem AddressedEnvironment.Realizes.write {current : AddressedEnvironment}
    {context : List (BindingId × BindingType)} {slot : BindingType}
    (realized : current.Realizes program context)
    (resolved : lookup place.root context = some slot)
    (checked : PathType program home slot.type place.fields type)
    (writable : slot.mutable = true)
    {value : Value} (resident : ValueHasType program value type) :
    ∃ after, current.write program place value = some after ∧ after.Realizes program context ∧
      after.read program place = some value ∧ AddressedEnvironment.Frames context current after ∧
      after.supply = current.supply ∧
      after.heap.next = current.heap.next ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program current.heap caller.activation caller.bindings states →
        caller.activation ≠ current.activation → BindingMap.Typed program after.heap caller.activation caller.bindings states ∧
          (∀ identity ∈ caller.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity)) := by
  have beforeRealized := realized
  have sourceResolved := resolved
  obtain ⟨⟨states, typed, slots, ready⟩, issued⟩ := realized
  rw [← slots, lookup.map] at resolved
  obtain ⟨state, selected, sameSlot⟩ := Option.map_eq_some_iff.mp resolved
  have checkedState : PathType program home state.slot.type place.fields type := by
    rw [sameSlot]; exact checked
  obtain ⟨after, nextState, nextContext, written, stateWritten, replaced, afterTyped,
    readback, scope, supply, next, initialized, retained⟩ :=
    AddressedEnvironment.write.progress typed selected checkedState resident
  have projected := replaceBinding.map_same BindingState.slot selected replaced rfl
  have nextReady := replaceBinding.all (predicate := fun state : BindingState => state.initialization.Ready) replaced ready
    (initialized (ready (place.root, state) (lookup.mem selected)))
  have activation : after.activation = current.activation := congrArg AddressedScope.activation scope
  refine ⟨after, written, ⟨⟨nextContext, afterTyped, projected.trans slots, nextReady⟩, ?_⟩,
    readback, AddressedEnvironment.write.frame beforeRealized sourceResolved writable written, supply, next, retained⟩
  rw [supply, activation]
  exact issued


theorem AddressedEnvironment.Realizes.extend {current : AddressedEnvironment}
    {context : List (BindingId × BindingType)} {inputs : List BindingInput}
    (realized : current.Realizes program context) (inputsTyped : BindingInputsTyped program inputs)
    (fresh : (inputs.map BindingInput.name ++ context.map Prod.fst).Nodup) :
    (current.extend inputs).Realizes program ((inputs.map fun input => (input.name, input.slot)) ++ context) ∧
    (∀ caller callerContext, AddressedScope.Realizes caller program current.heap callerContext →
      caller.Realizes program (current.extend inputs).heap callerContext ∧
      (∀ identity ∈ caller.bindings.map Prod.snd, (current.extend inputs).heap.read identity = current.heap.read identity)) := by
  obtain ⟨⟨states, typed, slots, ready⟩, issued⟩ := realized
  have keys := congrArg (List.map Prod.fst) slots
  simp only [List.map_map, Function.comp_def] at keys
  have freshStates : (inputs.map BindingInput.name ++ states.map Prod.fst).Nodup := by
    rw [keys]; exact fresh
  obtain ⟨afterTyped, _, _, retained⟩ := AddressedEnvironment.extend.typed typed inputsTyped freshStates
  refine ⟨⟨⟨inputs.map BindingInput.state ++ states, afterTyped, ?_, ?_⟩, issued⟩, ?_⟩
  · simp only [List.map_append, slots, List.map_map, BindingInput.state, Function.comp_def]
  · intro entry member
    rcases List.mem_append.mp member with fresh | old
    · obtain ⟨input, _, same⟩ := List.mem_map.mp fresh
      subst entry
      exact .present
    · exact ready entry old
  · intro caller callerContext callerRealized
    obtain ⟨callerStates, callerTyped, callerSlots, callerReady⟩ := callerRealized
    obtain ⟨afterTyped, preserved⟩ := retained _ _ _ callerTyped
    exact ⟨⟨callerStates, afterTyped, callerSlots, callerReady⟩, preserved⟩

theorem AddressedEnvironment.Realizes.exitScope {current : AddressedEnvironment}
    {context : List (BindingId × BindingType)} (realized : current.Realizes program context) (count : Nat) :
    ∃ after, current.exitScope count = some after ∧ after.Realizes program (context.drop count) ∧
      after.activation = current.activation ∧ after.supply = current.supply ∧
      after.heap.next = current.heap.next ∧
      (∀ identity ∈ (List.take count current.bindings).map Prod.snd, after.heap.Retired identity) ∧
      (∀ caller callerContext, AddressedScope.Realizes caller program current.heap callerContext →
        caller.activation ≠ current.activation → caller.Realizes program after.heap callerContext ∧
        (∀ identity ∈ caller.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity)) ∧
      (∀ identity ∈ after.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity) := by
  obtain ⟨⟨states, typed, slots, ready⟩, issued⟩ := realized
  obtain ⟨after, exited, afterTyped, activation, supply, next, retired, retained, preserved⟩ :=
    AddressedEnvironment.exitScope.progress typed count
  refine ⟨after, exited, ⟨⟨states.drop count, afterTyped, ?_, ?_⟩, ?_⟩,
    activation, supply, next, retired, ?_, preserved⟩
  · rw [List.map_drop, slots]
  · intro entry member
    exact ready entry (List.mem_of_mem_drop member)
  · rw [supply, activation]
    exact issued
  · intro caller callerContext callerRealized different
    obtain ⟨callerStates, callerTyped, callerSlots, callerReady⟩ := callerRealized
    obtain ⟨callerAfter, callerPreserved⟩ := retained _ _ callerTyped different
    exact ⟨⟨callerStates, callerAfter, callerSlots, callerReady⟩, callerPreserved⟩

theorem AddressedEnvironment.Realizes.restore {current : AddressedEnvironment}
    {locals context : List (BindingId × BindingType)} {caller : AddressedScope}
    (realized : current.Realizes program locals)
    (callerRealized : caller.Realizes program current.heap context)
    (callerIssued : current.supply.Issued caller.activation)
    (different : caller.activation ≠ current.activation) :
    ∃ after, current.restore caller = some after ∧ after.Realizes program context ∧
      after.scope = caller ∧ after.supply = current.supply ∧ after.heap.next = current.heap.next ∧
      (∀ identity ∈ current.bindings.map Prod.snd, after.heap.Retired identity) ∧
      (∀ identity ∈ caller.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity) ∧
      (∀ place, after.read program place = caller.bindings.read program current.heap place) ∧
      (∀ retained retainedContext, AddressedScope.Realizes retained program current.heap retainedContext →
        retained.activation ≠ current.activation →
        retained.Realizes program after.heap retainedContext ∧
        (∀ identity ∈ retained.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity)) := by
  obtain ⟨⟨states, typed, _, _⟩, _⟩ := realized
  obtain ⟨callerStates, callerTyped, callerSlots, callerReady⟩ := callerRealized
  obtain ⟨after, restored, afterTyped, activation, bindings, supply, next, retired, preserved, retained⟩ :=
    AddressedEnvironment.restore.progress typed callerTyped different
  have realizedAfter : after.Realizes program context := by
    refine ⟨⟨callerStates, ?_, callerSlots, callerReady⟩, ?_⟩
    · change BindingMap.Typed program after.heap after.activation after.bindings callerStates
      rw [activation, bindings]
      exact afterTyped
    · rw [supply, activation]
      exact callerIssued
  refine ⟨after, restored, realizedAfter, ?_, supply, next, retired, preserved, ?_, ?_⟩
  · change (⟨after.activation, after.bindings⟩ : AddressedScope) = caller
    rw [activation, bindings]
  · intro place
    change after.bindings.read program after.heap place = _
    rw [bindings]
    exact BindingMap.read.frame preserved
  · intro scope scopeContext scopeRealized apart
    obtain ⟨scopeStates, scopeTyped, scopeSlots, scopeReady⟩ := scopeRealized
    obtain ⟨scopeAfter, scopePreserved⟩ := retained scope scopeStates scopeTyped apart
    exact ⟨⟨scopeStates, scopeAfter, scopeSlots, scopeReady⟩, scopePreserved⟩


theorem AddressedEnvironment.Realizes.keys {current : AddressedEnvironment}
    {context : List (BindingId × BindingType)} (realized : current.Realizes program context) :
    current.bindings.map Prod.fst = context.map Prod.fst := by
  obtain ⟨⟨states, typed, slots, _⟩, _⟩ := realized
  rw [← slots, List.map_map]
  exact typed.keys

theorem AddressedEnvironment.Realizes.distinct {current : AddressedEnvironment}
    {context : List (BindingId × BindingType)} (realized : current.Realizes program context) :
    (context.map Prod.fst).Nodup := by
  obtain ⟨⟨states, typed, slots, ready⟩, _⟩ := realized
  rw [← slots, List.map_map]
  have distinct : (states.map Prod.fst).Nodup := by
    clear slots ready
    generalize current.scope.bindings = bindings at typed
    induction typed with
    | nil => exact .nil
    | cons found owner declared resident tail freshName freshStorage ih =>
      exact List.nodup_cons.mpr ⟨freshName, ih⟩
  exact distinct

theorem BindingInputsTyped.enter {inputs : List BindingInput} (typed : BindingInputsTyped program inputs)
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    (enterBindings heap supply inputs).Realizes program (inputs.map fun input => (input.name, input.slot)) ∧
    (∀ caller context, AddressedScope.Realizes caller program heap context →
      caller.Realizes program (enterBindings heap supply inputs).heap context ∧
      (∀ identity ∈ caller.bindings.map Prod.snd, (enterBindings heap supply inputs).heap.read identity = heap.read identity)) := by
  refine ⟨⟨⟨inputs.map BindingInput.state, enterBindings.typed typed heap supply, ?_, ?_⟩,
    supply.allocate_issued⟩, ?_⟩
  · simp [BindingInput.state, List.map_map, Function.comp_def]
  · intro entry member
    obtain ⟨input, _, same⟩ := List.mem_map.mp member
    subst entry
    exact .present
  · intro caller context realized
    obtain ⟨states, callerTyped, slots, ready⟩ := realized
    exact ⟨⟨states, callerTyped.allocate supply.allocate.1 inputs, slots, ready⟩,
      callerTyped.allocate_preserves supply.allocate.1 inputs⟩


/-- Realize a scope view without retiring storage. Execution still uses exitScope. -/
theorem AddressedEnvironment.Realizes.drop {current : AddressedEnvironment}
    {context : List (BindingId × BindingType)} (realized : current.Realizes program context) (count : Nat) :
    ({ current with bindings := current.bindings.drop count } : AddressedEnvironment).Realizes program (context.drop count) := by
  obtain ⟨⟨states, typed, slots, ready⟩, issued⟩ := realized
  refine ⟨⟨states.drop count, typed.drop count, ?_, ?_⟩, issued⟩
  · rw [List.map_drop, slots]
  · intro entry member
    exact ready entry (List.mem_of_mem_drop member)

theorem AddressedEnvironment.Frames.drop {before after : AddressedEnvironment}
    {context : List (BindingId × BindingType)} (realized : before.Realizes program context)
    (framed : Frames context before after) (count : Nat) :
    Frames (context.drop count) { before with bindings := before.bindings.drop count }
      { after with bindings := after.bindings.drop count } := by
  refine ⟨congrArg (fun scope : AddressedScope =>
    (⟨scope.activation, scope.bindings.drop count⟩ : AddressedScope)) framed.1, ?_⟩
  intro name slot identity selected immutable mapped
  apply framed.2 name slot identity
    (lookup.of_mem realized.distinct (List.mem_of_mem_drop (lookup.mem selected))) immutable
  apply lookup.of_mem _ (List.mem_of_mem_drop (lookup.mem mapped))
  rw [realized.keys]
  exact realized.distinct


theorem AddressedEnvironment.Frames.of_cells {context : List (BindingId × BindingType)}
    {before after : AddressedEnvironment} (scope : after.scope = before.scope)
    (preserved : ∀ identity ∈ before.bindings.map Prod.snd, after.heap.read identity = before.heap.read identity) :
    Frames context before after := by
  refine ⟨scope, ?_⟩
  intro name slot identity selected immutable mapped
  exact preserved identity (List.mem_map.mpr ⟨(name, identity), lookup.mem mapped, rfl⟩)

theorem AddressedScope.Realizes.allocate_preserves {scope : AddressedScope} {heap : RuntimeHeap StorageCell}
    {context : List (BindingId × BindingType)} (realized : scope.Realizes program heap context)
    (owner : ActivationId) (inputs : List BindingInput) :
    ∀ identity ∈ scope.bindings.map Prod.snd, (allocateBindings heap owner inputs).2.read identity = heap.read identity := by
  obtain ⟨states, typed, _, _⟩ := realized
  exact typed.allocate_preserves owner inputs


end Grounded
