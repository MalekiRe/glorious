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

def BindingState.Disposable (data : DataDeclarations) (state : BindingState) : Prop :=
  state.initialization.Disposable data state.slot.type

inductive BindingInputsTyped (program : Program) : List BindingInput → Prop where
  | nil : BindingInputsTyped program []
  | cons {input : BindingInput} {rest : List BindingInput}
      (resident : ValueHasType program input.value input.slot.type)
      (tail : BindingInputsTyped program rest)
      (fresh : input.name ∉ rest.map BindingInput.name) :
      BindingInputsTyped program (input :: rest)

theorem BindingInputsTyped.append {program : Program} {front back : List BindingInput}
    (first : BindingInputsTyped program front) (rest : BindingInputsTyped program back)
    (distinct : ((front ++ back).map BindingInput.name).Nodup) :
    BindingInputsTyped program (front ++ back) := by
  induction first with
  | nil => exact rest
  | cons resident tail fresh ih =>
    have parts := List.nodup_cons.mp distinct
    exact .cons resident (ih parts.2) parts.1

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

/-- A binding batch changes no storage identity outside its actual outputs. -/
theorem allocateBindings.outside (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    (inputs : List BindingInput) {identity : StorageId}
    (outside : identity ∉ (allocateBindings heap activation inputs).1.map Prod.snd) :
    (allocateBindings heap activation inputs).2.read identity = heap.read identity := by
  induction inputs generalizing heap with
  | nil => rfl
  | cons input rest ih =>
    simp only [allocateBindings, List.map_cons, List.mem_cons, not_or] at outside
    exact (ih _ outside.2).trans (RuntimeHeap.allocate_other _ _ _ outside.1)

theorem allocateBindings.history (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    (inputs : List BindingInput) : RuntimeHeap.History heap (allocateBindings heap activation inputs).2 := by
  induction inputs generalizing heap with
  | nil => exact .refl _
  | cons input rest ih => exact .step (.allocate heap (input.cell activation)) (ih _)


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

/-- Joined contexts preserve binding identity, declared type and mutability.
Only discardable occupancy may lose branch correlation. -/
inductive BindingContextApprox (data : DataDeclarations) : List (BindingId × BindingState) → List (BindingId × BindingState) → Prop where
  | nil : BindingContextApprox data [] []
  | cons {name slot before after rest tail}
      (head : Initialization.Approximates data slot.type before after) (remaining : BindingContextApprox data rest tail) :
      BindingContextApprox data ((name, ⟨slot, before⟩) :: rest) ((name, ⟨slot, after⟩) :: tail)

theorem BindingContextApprox.refl {data : DataDeclarations} (context : List (BindingId × BindingState)) : BindingContextApprox data context context := by
  induction context with
  | nil => exact .nil
  | cons entry rest ih => exact .cons .refl ih

theorem BindingContextApprox.slots {data : DataDeclarations} {before after : List (BindingId × BindingState)}
    (approximation : BindingContextApprox data before after) :
    after.map (fun entry => (entry.1, entry.2.slot)) = before.map (fun entry => (entry.1, entry.2.slot)) := by
  induction approximation with
  | nil => rfl
  | cons head remaining ih => simp only [List.map_cons, ih]

theorem BindingContextApprox.keys {data : DataDeclarations} {before after : List (BindingId × BindingState)}
    (approximation : BindingContextApprox data before after) : after.map Prod.fst = before.map Prod.fst := by
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) approximation.slots

theorem BindingMap.Typed.approximate {program : Program} {heap : RuntimeHeap StorageCell}
    {activation : ActivationId} {bindings : BindingMap} {before after : List (BindingId × BindingState)}
    (typed : BindingMap.Typed program heap activation bindings before) (approximation : BindingContextApprox program.data before after) :
    BindingMap.Typed program heap activation bindings after := by
  induction approximation generalizing bindings with
  | nil => cases typed; exact .nil
  | cons head remaining ih =>
    cases typed with
    | cons found owner declared resident tail freshName freshStorage =>
      exact .cons found owner declared ⟨resident.1, resident.2.approximate (by simpa only [declared] using head)⟩ (ih tail)
        (by simpa only [remaining.keys] using freshName) freshStorage


theorem BindingContextApprox.lookup {data : DataDeclarations}
    {before after : List (BindingId × BindingState)} (joined : BindingContextApprox data before after)
    {name : BindingId} {state : BindingState} (selected : Grounded.lookup name before = some state) :
    ∃ next, Grounded.lookup name after = some ⟨state.slot, next⟩ ∧
      state.initialization.Approximates data state.slot.type next := by
  induction joined with
  | nil => simp [Grounded.lookup] at selected
  | cons head tail ih =>
    simp only [Grounded.lookup] at selected ⊢
    split at selected
    next same =>
      cases selected
      exact ⟨_, by simp [same], head⟩
    next different =>
      simpa only [if_neg different] using ih selected


variable {program : Program} {heap after : RuntimeHeap StorageCell} {activation : ActivationId}
    {bindings : BindingMap} {context : List (BindingId × BindingState)}

/-- Physical residents eligible for scope retirement. This predicate inspects
the same heap cells selected by the runtime binding map. -/
def BindingMap.Disposable (program : Program) (heap : RuntimeHeap StorageCell) (bindings : BindingMap) : Prop :=
  ∀ identity ∈ bindings.map Prod.snd, ∃ cell, heap.read identity = some cell ∧
    cell.resident.Disposable program cell.type

theorem BindingMap.Typed.disposable (typed : BindingMap.Typed program heap activation bindings context)
    (disposition : ∀ binding ∈ context, binding.2.Disposable program.data) :
    BindingMap.Disposable program heap bindings := by
  induction typed with
  | nil => intro identity member; simp at member
  | @cons name identity cell state bindings context found owner declared resident tail freshName freshStorage ih =>
    intro address member
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · refine ⟨cell, found, ?_⟩
      have permission : state.initialization.Disposable program.data cell.type := by
        rw [declared]; exact disposition (name, state) (by simp)
      exact permission.realizes resident.2
    · exact ih (fun binding included => disposition binding (List.mem_cons_of_mem _ included)) address member

theorem BindingMap.Typed.keys (typed : BindingMap.Typed program heap activation bindings context) :
    bindings.map Prod.fst = context.map Prod.fst := by
  induction typed with
  | nil => rfl
  | cons found owner declared resident tail freshName freshStorage ih => exact congrArg (List.cons _) ih

theorem BindingMap.Typed.context_distinct (typed : BindingMap.Typed program heap activation bindings context) :
    (context.map Prod.fst).Nodup := by
  induction typed with
  | nil => exact .nil
  | cons found owner declared resident tail freshName freshStorage ih =>
    exact List.nodup_cons.mpr ⟨freshName, ih⟩

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

theorem BindingMap.Typed.owns (typed : BindingMap.Typed program heap activation bindings context)
    {identity : StorageId} {cell : StorageCell} (member : identity ∈ bindings.map Prod.snd)
    (found : heap.read identity = some cell) : cell.activation = activation := by
  induction typed with
  | nil => simp at member
  | cons here owner declared resident tail freshName freshStorage ih =>
    cases member with
    | head => cases Option.some.inj (found.symm.trans here); exact owner
    | tail _ member => exact ih member

theorem BindingMap.Typed.apart_activations
    (first : BindingMap.Typed program heap activation bindings context)
    {otherActivation : ActivationId} {otherBindings : BindingMap}
    {otherContext : List (BindingId × BindingState)}
    (second : BindingMap.Typed program heap otherActivation otherBindings otherContext)
    (different : activation ≠ otherActivation) :
    ∀ identity ∈ bindings.map Prod.snd, identity ∉ otherBindings.map Prod.snd := by
  intro identity member otherMember
  obtain ⟨cell, found⟩ := first.live identity member
  exact different ((first.owns member found).symm.trans (second.owns otherMember found))

/-- Exact cell framing transports realization; no post-state typing premise. -/
theorem BindingMap.Typed.frame (typed : BindingMap.Typed program heap activation bindings context)
    (unchanged : ∀ identity ∈ bindings.map Prod.snd, after.read identity = heap.read identity) :
    BindingMap.Typed program after activation bindings context := by
  induction typed with
  | nil => exact .nil
  | cons found owner declared resident tail freshName freshStorage ih =>
    exact .cons ((unchanged _ (by simp)).trans found) owner declared resident
      (ih (fun identity member => unchanged identity (List.mem_cons_of_mem _ member))) freshName freshStorage

/-- Retiring other cells cannot revoke cleanup permission for a retained
resident. The surviving map removes exactly the identities actually retired. -/
theorem BindingMap.Disposable.retirement_prefix
    (disposition : BindingMap.Disposable program heap bindings)
    {retired : List StorageId} {middle : RuntimeHeap StorageCell}
    (executed : heap.retireMany retired = some middle) :
    BindingMap.Disposable program middle
      (bindings.filter fun entry => decide (entry.2 ∉ retired)) := by
  intro identity member
  obtain ⟨entry, member, same⟩ := List.mem_map.mp member
  obtain ⟨included, keep⟩ := List.mem_filter.mp member
  have original := List.mem_map.mpr ⟨entry, included, same⟩
  obtain ⟨cell, found, permission⟩ := disposition identity original
  have outside : identity ∉ retired := by simpa only [decide_eq_true_eq, same] using keep
  exact ⟨cell, (RuntimeHeap.retireMany_outside executed outside).trans found, permission⟩
/-- Retain exactly the selected storage identities without changing any source
binding state. This transports masks, rather than reconstructing availability. -/
theorem BindingMap.Typed.filter_cells
    (typed : BindingMap.Typed program heap activation bindings context)
    (keep : StorageId → Bool) :
    ∃ remaining, remaining.Sublist context ∧
      BindingMap.Typed program heap activation (bindings.filter fun entry => keep entry.2) remaining := by
  induction typed with
  | nil => exact ⟨[], .refl _, .nil⟩
  | @cons name identity cell state bindings context found owner declared resident tail freshName freshStorage ih =>
    obtain ⟨remaining, subset, retained⟩ := ih
    cases chosen : keep identity with
    | false =>
      exact ⟨remaining, subset.cons _, by simpa [chosen] using retained⟩
    | true =>
      refine ⟨(name, state) :: remaining, subset.cons_cons _, ?_⟩
      simp only [List.filter_cons, chosen, ↓reduceIte]
      refine .cons found owner declared resident retained ?_ ?_
      · intro member
        obtain ⟨entry, member, same⟩ := List.mem_map.mp member
        exact freshName (List.mem_map.mpr ⟨entry, subset.subset member, same⟩)
      · intro member
        obtain ⟨entry, member, same⟩ := List.mem_map.mp member
        exact freshStorage (List.mem_map.mpr ⟨entry, (List.mem_filter.mp member).1, same⟩)

/-- Every actual retirement prefix leaves the not-yet-retired bindings realized
in that prefix's heap. Their source states are retained verbatim, not supplied
as a future-state invariant. -/
theorem BindingMap.Typed.retirement_prefix
    (typed : BindingMap.Typed program heap activation bindings context)
    {retired : List StorageId} {middle : RuntimeHeap StorageCell}
    (executed : heap.retireMany retired = some middle) :
    ∃ remaining, remaining.Sublist context ∧
      BindingMap.Typed program middle activation
        (bindings.filter fun entry => decide (entry.2 ∉ retired)) remaining := by
  obtain ⟨remaining, subset, retained⟩ := typed.filter_cells (fun identity => decide (identity ∉ retired))
  refine ⟨remaining, subset, retained.frame ?_⟩
  intro identity member
  obtain ⟨entry, member, same⟩ := List.mem_map.mp member
  have outside := (List.mem_filter.mp member).2
  simp only [decide_eq_true_eq] at outside
  exact RuntimeHeap.retireMany_outside executed (same ▸ outside)
/-- A write confined to one owned cell preserves every differently owned map.
The address separation follows from the cell’s owner, not lexical spelling. -/
theorem BindingMap.Typed.frame_other_activation
    (typed : BindingMap.Typed program heap activation bindings context)
    {identity : StorageId} {cell : StorageCell} (found : heap.read identity = some cell)
    (different : activation ≠ cell.activation)
    (unchanged : ∀ other, other ≠ identity → after.read other = heap.read other) :
    BindingMap.Typed program after activation bindings context ∧
      (∀ other ∈ bindings.map Prod.snd, after.read other = heap.read other) := by
  have preserved : ∀ other ∈ bindings.map Prod.snd, after.read other = heap.read other := by
    intro other member
    apply unchanged other
    intro same
    subst other
    exact different (typed.owns member found).symm
  exact ⟨typed.frame preserved, preserved⟩

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

/-- Ordered argument and pattern batches acquire storage from oldest to newest. -/
theorem allocateBindings.increasing (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    (inputs : List BindingInput) :
    ((allocateBindings heap activation inputs).1.map Prod.snd).Pairwise
      (fun older newer => older.index < newer.index) := by
  induction inputs generalizing heap with
  | nil => exact .nil
  | cons input rest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih _⟩
    intro identity member
    have bound := allocateBindings.bounds (heap.allocate (input.cell activation)).2 activation rest identity member
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) bound


theorem allocateBindings.keys (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    (inputs : List BindingInput) :
    (allocateBindings heap activation inputs).1.map Prod.fst = inputs.map BindingInput.name := by
  induction inputs generalizing heap with
  | nil => rfl
  | cons input rest ih => exact congrArg (List.cons input.name) (ih _)
/-- The real input at each position becomes a live cell at a distinct fresh
identity. No value, declaration type or activation is reconstructed afterwards. -/
theorem allocateBindings.at (heap : RuntimeHeap StorageCell) (activation : ActivationId)
    {inputs : List BindingInput} {index : Nat} {input : BindingInput}
    (selected : inputs[index]? = some input) :
    ∃ identity, (allocateBindings heap activation inputs).1[index]? = some (input.name, identity) ∧
      (allocateBindings heap activation inputs).2.read identity = some (input.cell activation) ∧
      identity.index = heap.next + index := by
  induction inputs generalizing heap index with
  | nil => simp at selected
  | cons first rest ih =>
    cases index with
    | zero =>
      cases selected
      exact ⟨_, rfl, (allocateBindings.old (heap.allocate (input.cell activation)).2 activation rest
        (Nat.lt_succ_self _)).trans (heap.allocate_read _), rfl⟩
    | succ index =>
      obtain ⟨identity, found, resident, position⟩ := ih (heap.allocate (first.cell activation)).2 selected
      refine ⟨identity, found, resident, ?_⟩
      simpa only [RuntimeHeap.allocate, Nat.add_assoc, Nat.add_comm 1 index] using position

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
theorem BindingMap.Typed.allocate_preserves (typed : BindingMap.Typed program heap activation bindings context)
    (owner : ActivationId) (inputs : List BindingInput) :
    ∀ identity ∈ bindings.map Prod.snd,
      (allocateBindings heap owner inputs).2.read identity = heap.read identity := by
  intro identity member
  obtain ⟨cell, found⟩ := typed.live identity member
  exact allocateBindings.old heap owner inputs (heap.bounded identity cell found)

theorem BindingMap.Typed.allocate (typed : BindingMap.Typed program heap activation bindings context)
    (owner : ActivationId) (inputs : List BindingInput) :
    BindingMap.Typed program (allocateBindings heap owner inputs).2 activation bindings context :=
  typed.frame (typed.allocate_preserves owner inputs)

/-- Binding presentation order is lexical, not acquisition order. Fresh storage
identities already record acquisition order, including ordered parameter batches. -/
def BindingMap.releaseOrder (bindings : BindingMap) : List StorageId :=
  (bindings.map Prod.snd).mergeSort (fun older newer => decide (newer.index ≤ older.index))

theorem BindingMap.releaseOrder_perm (bindings : BindingMap) :
    bindings.releaseOrder.Perm (bindings.map Prod.snd) :=
  List.mergeSort_perm _ _

@[simp] theorem BindingMap.mem_releaseOrder {bindings : BindingMap} {identity : StorageId} :
    identity ∈ bindings.releaseOrder ↔ identity ∈ bindings.map Prod.snd :=
  bindings.releaseOrder_perm.mem_iff

/-- Every later retirement is strictly older; each owned cell occurs exactly
once because typed binding maps are injective in storage identity. -/
theorem BindingMap.releaseOrder_decreasing (bindings : BindingMap)
    (distinct : (bindings.map Prod.snd).Nodup) :
    bindings.releaseOrder.Pairwise (fun newer older => older.index < newer.index) := by
  have sorted := List.pairwise_mergeSort
    (le := fun left right : StorageId => decide (right.index ≤ left.index))
    (by intro a b c first second; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (bindings.map Prod.snd)
  have weak : bindings.releaseOrder.Pairwise (fun a b => b.index ≤ a.index) := by
    simpa only [BindingMap.releaseOrder, decide_eq_true_eq] using sorted
  have unequal : bindings.releaseOrder.Nodup := bindings.releaseOrder_perm.nodup_iff.mpr distinct
  apply (weak.and unequal).imp
  intro a b pair
  have different : a.index ≠ b.index := by
    intro same
    apply pair.2
    cases a; cases b; simpa using same
  omega

/-- Source-ordered parameter acquisition is released in reverse acquisition
order. This follows for arbitrary batches, not a distinguished two-input case. -/
theorem allocateBindings.releaseOrder_reverse (heap : RuntimeHeap StorageCell)
    (activation : ActivationId) (inputs : List BindingInput) :
    (allocateBindings heap activation inputs).1.releaseOrder =
      ((allocateBindings heap activation inputs).1.map Prod.snd).reverse := by
  have increasing := allocateBindings.increasing heap activation inputs
  have distinct : ((allocateBindings heap activation inputs).1.map Prod.snd).Nodup := by
    apply increasing.imp
    intro a b older same
    cases same
    exact Nat.lt_irrefl _ older
  have first := BindingMap.releaseOrder_decreasing _ distinct
  have second := List.pairwise_reverse.mpr increasing
  apply List.Perm.eq_of_pairwise (le := fun newer older : StorageId => older.index < newer.index)
    (fun _ _ _ _ forward backward => False.elim (Nat.lt_asymm forward backward)) first second
  exact (BindingMap.releaseOrder_perm _).trans (List.reverse_perm _).symm


/-- Scope release retires actual owners newest-first, independently of lexical
name order. Disposal permission remains the responsibility of source checking. -/
def releaseBindings (heap : RuntimeHeap StorageCell) (bindings : BindingMap) : Option (RuntimeHeap StorageCell) :=
  heap.retireMany bindings.releaseOrder

theorem releaseBindings.outside {heap after : RuntimeHeap StorageCell} {bindings : BindingMap}
    (released : releaseBindings heap bindings = some after) {identity : StorageId}
    (outside : identity ∉ bindings.map Prod.snd) : after.read identity = heap.read identity :=
  RuntimeHeap.retireMany_outside released (by simpa only [BindingMap.mem_releaseOrder] using outside)

theorem releaseBindings.retired {heap after : RuntimeHeap StorageCell} {bindings : BindingMap}
    (released : releaseBindings heap bindings = some after) :
    ∀ identity ∈ bindings.map Prod.snd, after.Retired identity := by
  intro identity member
  exact RuntimeHeap.retireMany_retired released identity
    (by simpa only [BindingMap.mem_releaseOrder] using member)

/-- Factor the actual shared retirement operation at any point. Its next
retirement precedes only strictly older owners, not merely an unordered set of
final absences. The witnesses are the intermediate heaps used by retireMany. -/
theorem releaseBindings.prefix_step {heap after : RuntimeHeap StorageCell} {bindings : BindingMap}
    (released : releaseBindings heap bindings = some after)
    (ordered : bindings.releaseOrder.Pairwise (fun newer older => older.index < newer.index))
    {front back : List StorageId} {identity : StorageId}
    (split : bindings.releaseOrder = front ++ identity :: back) :
    ∃ middle next, heap.retireMany front = some middle ∧
      middle.retire identity = some next ∧ next.retireMany back = some after ∧
      ∀ older ∈ back, older.index < identity.index := by
  change heap.retireMany bindings.releaseOrder = some after at released
  rw [split, RuntimeHeap.retireMany_append] at released
  obtain ⟨middle, prefixRun, remaining⟩ := Option.bind_eq_some_iff.mp released
  obtain ⟨next, retired, suffixRun⟩ := Option.bind_eq_some_iff.mp remaining
  refine ⟨middle, next, prefixRun, retired, suffixRun, ?_⟩
  rw [split] at ordered
  exact (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1


/-- Earlier retirements preserve the actual resident and its residual disposal
permission until this owner's turn. No intermediate heap readiness is assumed. -/
theorem BindingMap.Disposable.release_prefix
    (disposition : BindingMap.Disposable program heap bindings)
    {after : RuntimeHeap StorageCell} (released : releaseBindings heap bindings = some after)
    (ordered : bindings.releaseOrder.Pairwise (fun newer older => older.index < newer.index))
    {front back : List StorageId} {identity : StorageId}
    (split : bindings.releaseOrder = front ++ identity :: back) :
    ∃ middle next, heap.retireMany front = some middle ∧
      middle.retire identity = some next ∧ next.retireMany back = some after ∧
      (∀ older ∈ back, older.index < identity.index) ∧
      ∃ cell, heap.read identity = some cell ∧ middle.read identity = some cell ∧
        cell.resident.Disposable program cell.type ∧
        ∀ (observer : Module) (fields : List FieldKey) (nominal : Nat) (declaration : DataDecl),
          PathType program observer cell.type fields (.nominal nominal) →
          program.data nominal = some declaration → declaration.restriction = some .exact →
          ∃ part, cell.resident.selectFields program cell.type fields = some part ∧ part.Empty := by
  obtain ⟨middle, next, prefixRun, retired, suffixRun, older⟩ :=
    releaseBindings.prefix_step released ordered split
  have member : identity ∈ bindings.map Prod.snd := by
    apply BindingMap.mem_releaseOrder.mp
    rw [split]
    simp
  obtain ⟨cell, found, permission⟩ := disposition identity member
  have outside : identity ∉ front := by
    intro included
    rw [split] at ordered
    exact Nat.lt_irrefl _ ((List.pairwise_append.mp ordered).2.2 identity included identity (by simp))
  refine ⟨middle, next, prefixRun, retired, suffixRun, older, cell, found,
    (RuntimeHeap.retireMany_outside prefixRun outside).trans found, permission, ?_⟩
  intro observer fields nominal declaration path declared restricted
  obtain ⟨part, selected, disposable⟩ := path.disposable permission
  exact ⟨part, selected, disposable.exact_nominal_empty declared restricted⟩


/-- A live nondiscardable descendant protects its entire containing cell from
retirement, including when other fields have been consumed. -/
theorem BindingMap.Disposable.release_preserves_nondiscardable
    (disposition : BindingMap.Disposable program heap bindings)
    {after : RuntimeHeap StorageCell} (released : releaseBindings heap bindings = some after)
    {address : StorageId} {cell : StorageCell} (found : heap.read address = some cell)
    {selectedHome : Module} {selectedType : Ty} {fields : List FieldKey}
    (path : PathType program selectedHome cell.type fields selectedType)
    {owner : PartialValue}
    (resident : cell.resident.selectFields program cell.type fields = some owner)
    (required : ¬ owner.Disposable program selectedType) :
    after.read address = some cell := by
  have outside : address ∉ bindings.map Prod.snd := by
    intro member
    obtain ⟨actual, selected, permission⟩ := disposition address member
    cases Option.some.inj (selected.symm.trans found)
    obtain ⟨part, partFound, partPermission⟩ := path.disposable permission
    cases Option.some.inj (partFound.symm.trans resident)
    exact required partPermission
  exact (releaseBindings.outside released outside).trans found


/-- A partially consumed exact descendant protects its entire containing cell.
Successful whole-owner readback is not required to preserve its obligation. -/
theorem BindingMap.Disposable.release_preserves_exact
    (disposition : BindingMap.Disposable program heap bindings)
    {after : RuntimeHeap StorageCell} (released : releaseBindings heap bindings = some after)
    {address : StorageId} {cell : StorageCell} (found : heap.read address = some cell)
    {identity : Nat} {declaration : DataDecl} {selectedHome : Module} {fields : List FieldKey}
    (path : PathType program selectedHome cell.type fields (.nominal identity))
    (declared : program.data identity = some declaration) (restricted : declaration.restriction = some .exact)
    {owner : PartialValue} (resident : cell.resident.selectFields program cell.type fields = some owner)
    (unconsumed : ¬ owner.Empty) :
    after.read address = some cell := by
  exact disposition.release_preserves_nondiscardable released found path resident
    (fun permission => unconsumed (permission.exact_nominal_empty declared restricted))


theorem BindingMap.Typed.release (typed : BindingMap.Typed program heap activation bindings context) :
    ∃ after, releaseBindings heap bindings = some after ∧
      after.next = heap.next ∧
      (∀ identity ∈ bindings.map Prod.snd, after.Retired identity) ∧
      (∀ identity, identity ∉ bindings.map Prod.snd → after.read identity = heap.read identity) := by
  obtain ⟨after, released⟩ := heap.retireMany_exists bindings.releaseOrder
    (bindings.releaseOrder_perm.nodup_iff.mpr typed.addresses_distinct)
    (fun identity member => typed.live identity (BindingMap.mem_releaseOrder.mp member))
  exact ⟨after, released, RuntimeHeap.retireMany_next released,
    releaseBindings.retired released, fun _ outside => releaseBindings.outside released outside⟩

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
      (∀ identity ∈ bindings.map Prod.snd, after.Retired identity) ∧
      (∀ identity ∈ retained.map Prod.snd, after.read identity = heap.read identity) := by
  obtain ⟨after, released, next, retired, outside⟩ := typed.release
  have preserved := fun identity member => outside identity (apart identity member)
  exact ⟨after, released, callerTyped.frame preserved, next, retired, preserved⟩

/-- Retained lexical scope metadata contains no heap or allocation supply. -/
structure AddressedScope where
  activation : ActivationId
  bindings : BindingMap

/-- One current addressed environment carries the shared heap and supplies.
Retaining its scope does not snapshot either of them. -/
structure AddressedEnvironment where
  activation : ActivationId
  supply : ActivationSupply
  bindings : BindingMap
  heap : RuntimeHeap StorageCell

def AddressedEnvironment.scope (current : AddressedEnvironment) : AddressedScope :=
  ⟨current.activation, current.bindings⟩

def AddressedEnvironment.restore (current : AddressedEnvironment) (caller : AddressedScope) :
    Option AddressedEnvironment :=
  (releaseBindings current.heap current.bindings).map fun heap =>
    { current with activation := caller.activation, bindings := caller.bindings, heap := heap }

theorem AddressedEnvironment.restore.progress {current : AddressedEnvironment} {caller : AddressedScope}
    {locals callerContext : List (BindingId × BindingState)}
    (localTyped : BindingMap.Typed program current.heap current.activation current.bindings locals)
    (callerTyped : BindingMap.Typed program current.heap caller.activation caller.bindings callerContext)
    (different : caller.activation ≠ current.activation) :
    ∃ after, current.restore caller = some after ∧
      BindingMap.Typed program after.heap caller.activation caller.bindings callerContext ∧
      after.activation = caller.activation ∧ after.bindings = caller.bindings ∧
      after.supply = current.supply ∧ after.heap.next = current.heap.next ∧
      (∀ identity ∈ current.bindings.map Prod.snd, after.heap.Retired identity) ∧
      (∀ identity ∈ caller.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity) ∧
      (∀ (retained : AddressedScope) states,
        BindingMap.Typed program current.heap retained.activation retained.bindings states →
        retained.activation ≠ current.activation →
        BindingMap.Typed program after.heap retained.activation retained.bindings states ∧
        (∀ identity ∈ retained.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity)) := by
  obtain ⟨heap, released, next, retired, outside⟩ := localTyped.release
  have retain : ∀ (scope : AddressedScope) states,
      BindingMap.Typed program current.heap scope.activation scope.bindings states →
      scope.activation ≠ current.activation →
      BindingMap.Typed program heap scope.activation scope.bindings states ∧
      (∀ identity ∈ scope.bindings.map Prod.snd, heap.read identity = current.heap.read identity) := by
    intro scope states typed apart
    have preserved := fun identity member => outside identity (typed.apart_activations localTyped apart identity member)
    exact ⟨typed.frame preserved, preserved⟩
  obtain ⟨retained, preserved⟩ := retain caller callerContext callerTyped different
  exact ⟨{ current with activation := caller.activation, bindings := caller.bindings, heap := heap },
    by simp [AddressedEnvironment.restore, released], retained, rfl, rfl, rfl, next, retired, preserved, retain⟩

/-- Dynamic invocation entry consumes the activation supply, even for an empty
argument list. Lexical declaration IDs do not determine either dynamic identity. -/
def enterBindings (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) (inputs : List BindingInput) :
    AddressedEnvironment :=
  let activation := supply.allocate
  let allocated := allocateBindings heap activation.1 inputs
  ⟨activation.1, activation.2, allocated.1, allocated.2⟩

theorem enterBindings.typed {inputs : List BindingInput} (typed : BindingInputsTyped program inputs)
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    BindingMap.Typed program (enterBindings heap supply inputs).heap (enterBindings heap supply inputs).activation
      (enterBindings heap supply inputs).bindings (inputs.map BindingInput.state) :=
  allocateBindings.typed typed heap supply.allocate.1

def AddressedEnvironment.empty : AddressedEnvironment := enterBindings RuntimeHeap.empty ⟨0⟩ []

theorem enterBindings.fresh_activation (heap : RuntimeHeap StorageCell) (supply : ActivationSupply)
    (inputs : List BindingInput) :
    (enterBindings heap supply inputs).activation.index = supply.next ∧
      (enterBindings heap supply inputs).supply.next = supply.next + 1 := ⟨rfl, rfl⟩



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
      (∀ identity ∈ (bindings.take count).map Prod.snd, after.Retired identity) ∧
      (∀ identity ∈ (bindings.drop count).map Prod.snd, after.read identity = heap.read identity) := by
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

theorem prepareBindings.arity {parameters : List (BindingId × BindingType)} {values : List Value}
    {inputs : List BindingInput} (prepared : prepareBindings parameters values = some inputs) :
    parameters.length = values.length := by
  induction parameters generalizing values inputs with
  | nil => cases values <;> simp_all [prepareBindings]
  | cons parameter parameters ih =>
    cases values with
    | nil => cases parameter; simp [prepareBindings] at prepared
    | cons value values =>
      cases parameter
      simp only [prepareBindings, Option.map_eq_some_iff] at prepared
      obtain ⟨tail, prepared, _⟩ := prepared
      exact congrArg Nat.succ (ih prepared)

theorem prepareBindings.exists {parameters : List (BindingId × BindingType)} {values : List Value}
    (typed : ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type))) :
    ∃ inputs, prepareBindings parameters values = some inputs := by
  induction parameters generalizing values with
  | nil => cases typed; exact ⟨[], rfl⟩
  | cons parameter parameters ih =>
    cases typed with
    | cons head tail =>
      rename_i value rest
      obtain ⟨inputs, prepared⟩ := ih tail
      exact ⟨⟨parameter.1, parameter.2, value⟩ :: inputs, by cases parameter; simp [prepareBindings, prepared]⟩

def initializedContext (parameters : List (BindingId × BindingType)) : List (BindingId × BindingState) :=
  parameters.map fun parameter => (parameter.1, ⟨parameter.2, .present⟩)

theorem prepareBindings.progress {parameters : List (BindingId × BindingType)} {values : List Value}
    (typed : ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type)))
    (distinct : (parameters.map Prod.fst).Nodup) :
    ∃ inputs, prepareBindings parameters values = some inputs ∧ BindingInputsTyped program inputs ∧
      (inputs.map fun input => (input.name, input.slot)) = parameters := by
  induction parameters generalizing values with
  | nil => cases typed; exact ⟨[], rfl, .nil, rfl⟩
  | cons parameter parameters ih =>
    cases typed with
    | cons head tail =>
      have parts := List.nodup_cons.mp distinct
      obtain ⟨inputs, prepared, inputsTyped, slots⟩ := ih tail parts.2
      have names := congrArg (List.map Prod.fst) slots
      simp only [List.map_map, Function.comp_def] at names
      refine ⟨⟨parameter.1, parameter.2, _⟩ :: inputs, ?_, .cons head inputsTyped ?_, ?_⟩
      · cases parameter; simp [prepareBindings, prepared]
      · rw [names]; exact parts.1
      · exact congrArg (List.cons parameter) slots

/-- Direct function entry uses the declaration's resolved slots and the common
invocation allocator. The entry result contains no checking certificate. -/
def enterFunction (heap : RuntimeHeap StorageCell) (supply : ActivationSupply)
    (declaration : FunctionDecl) (values : List Value) :
    Option AddressedEnvironment :=
  (prepareBindings declaration.parameters values).map (enterBindings heap supply)

theorem enterFunction.progress {declaration : FunctionDecl} {values : List Value}
    (arguments : ValuesHaveTypes program values (declaration.parameters.map (fun parameter => parameter.2.type)))
    (distinct : (declaration.parameters.map Prod.fst).Nodup)
    (heap : RuntimeHeap StorageCell) (supply : ActivationSupply) :
    ∃ entry, enterFunction heap supply declaration values = some entry ∧
      BindingMap.Typed program entry.heap entry.activation entry.bindings (initializedContext declaration.parameters) ∧
      entry.activation.index = supply.next ∧ entry.supply.next = supply.next + 1 ∧
      (¬supply.Issued entry.activation) ∧ entry.supply.Issued entry.activation ∧
      (∀ previous, supply.Issued previous → entry.supply.Issued previous ∧ previous ≠ entry.activation) ∧
      (∀ caller callerContext owner, BindingMap.Typed program heap owner caller callerContext →
        BindingMap.Typed program entry.heap owner caller callerContext ∧
        (∀ identity ∈ entry.bindings.map Prod.snd, identity ∉ caller.map Prod.snd) ∧
        (∀ identity ∈ caller.map Prod.snd, entry.heap.read identity = heap.read identity)) := by
  obtain ⟨inputs, prepared, inputsTyped, slots⟩ := prepareBindings.progress arguments distinct
  refine ⟨enterBindings heap supply inputs, by simp [enterFunction, prepared], ?_, rfl, rfl,
    supply.allocate_fresh, supply.allocate_issued, ?_, ?_⟩
  · have states : inputs.map BindingInput.state = initializedContext declaration.parameters := by
      rw [← slots]
      simp [initializedContext, BindingInput.state, List.map_map, Function.comp_def]
    rw [← states]; exact enterBindings.typed inputsTyped heap supply
  · intro previous issued
    exact ⟨ActivationSupply.allocate_preserves issued, ActivationSupply.allocate_distinct issued⟩
  · intro caller callerContext owner callerTyped
    exact ⟨callerTyped.allocate supply.allocate.1 inputs,
      (fun identity member oldMember => callerTyped.allocate_apart supply.allocate.1 inputs identity member identity oldMember rfl),
      callerTyped.allocate_preserves supply.allocate.1 inputs⟩


/-- Lexical extension allocates in the existing activation; invocation entry
alone advances the activation supply. -/
def AddressedEnvironment.extend (current : AddressedEnvironment) (inputs : List BindingInput) :
    AddressedEnvironment :=
  let allocated := allocateBindings current.heap current.activation inputs
  { current with bindings := allocated.1 ++ current.bindings, heap := allocated.2 }

theorem AddressedEnvironment.extend.typed {current : AddressedEnvironment}
    {inputs : List BindingInput} {context : List (BindingId × BindingState)}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings context)
    (inputsTyped : BindingInputsTyped program inputs)
    (fresh : (inputs.map BindingInput.name ++ context.map Prod.fst).Nodup) :
    BindingMap.Typed program (current.extend inputs).heap current.activation (current.extend inputs).bindings
      (inputs.map BindingInput.state ++ context) ∧
    (current.extend inputs).activation = current.activation ∧
    (current.extend inputs).supply = current.supply ∧
    (∀ owner bindings states, BindingMap.Typed program current.heap owner bindings states →
      BindingMap.Typed program (current.extend inputs).heap owner bindings states ∧
      (∀ identity ∈ bindings.map Prod.snd, (current.extend inputs).heap.read identity = current.heap.read identity)) := by
  exact ⟨allocateBindings.extend inputsTyped typed fresh, rfl, rfl,
    fun _ _ _ retained => ⟨retained.allocate current.activation inputs, retained.allocate_preserves current.activation inputs⟩⟩

def AddressedEnvironment.exitScope (current : AddressedEnvironment) (count : Nat) :
    Option AddressedEnvironment :=
  (releaseBindings current.heap (current.bindings.take count)).map fun heap =>
    { current with bindings := current.bindings.drop count, heap := heap }

theorem AddressedEnvironment.exitScope.progress {current : AddressedEnvironment}
    {context : List (BindingId × BindingState)}
    (typed : BindingMap.Typed program current.heap current.activation current.bindings context)
    (count : Nat) :
    ∃ after, current.exitScope count = some after ∧
      BindingMap.Typed program after.heap after.activation after.bindings (context.drop count) ∧
      after.activation = current.activation ∧ after.supply = current.supply ∧
      after.heap.next = current.heap.next ∧
      (∀ identity ∈ (current.bindings.take count).map Prod.snd, after.heap.Retired identity) ∧
      (∀ (caller : AddressedScope) states, BindingMap.Typed program current.heap caller.activation caller.bindings states →
        caller.activation ≠ current.activation →
        BindingMap.Typed program after.heap caller.activation caller.bindings states ∧
        (∀ identity ∈ caller.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity)) ∧
      (∀ identity ∈ after.bindings.map Prod.snd, after.heap.read identity = current.heap.read identity) := by
  obtain ⟨heap, released, remaining, next, retired, preserved⟩ := typed.exit_scope count
  refine ⟨{ current with bindings := current.bindings.drop count, heap := heap },
    by simp [AddressedEnvironment.exitScope, released], remaining, rfl, rfl, next, retired, ?_, preserved⟩
  intro caller states callerTyped different
  have framed : ∀ identity ∈ caller.bindings.map Prod.snd, heap.read identity = current.heap.read identity := by
    intro identity member
    exact releaseBindings.outside released
      (callerTyped.apart_activations (typed.take count) different identity member)
  exact ⟨callerTyped.frame framed, framed⟩

end Grounded
