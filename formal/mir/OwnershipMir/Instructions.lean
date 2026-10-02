import OwnershipMir.Places

namespace OwnershipMir

inductive Op (n : Nat) where
  | take (place : Place n) (mode : Extract)
  | put (place : Place n)
  | copy (place : Place n)
  | drop

/-- Raw execution has no ownership permission guard. Classification and
capabilities are checked independently; unsafe raw copies and drops can run. -/
def Op.exec {n : Nat} : Op n → State n → Option (State n)
  | .take p mode, state => do
    let lens ← p.find state.slots
    let value ← lens.selected
    let result ← mode.apply value
    match state.temp with
    | none => some ⟨p.write state.slots lens none, some result⟩
    | some _ => none
  | .put p, state => do
    let lens ← p.find state.slots
    let value ← state.temp
    if vacant lens.selected then
      some ⟨p.write state.slots lens (some value), none⟩
    else none
  | .copy p, state => do
    let lens ← p.find state.slots
    let value ← lens.selected
    match state.temp with
    | none => some {state with temp := some value}
    | some _ => none
  | .drop, state => match state.temp with
    | some _ => some {state with temp := none}
    | none => none

inductive Op.Checked {n : Nat} : Context n → Op n → Context n → Prop where
  | take {context p mode input output lens} (empty : context.temp = none)
      (found : p.find context.slots = some lens) (selected : lens.selected = some input)
      (layout : p.layout = input.layout id) (extract : mode.Checked input output) :
      Checked context (.take p mode) ⟨p.write context.slots lens none, some output⟩
  | put {context p shape lens} (resident : context.temp = some shape)
      (found : p.find context.slots = some lens) (vacant : Fits shape lens.selected) :
      Checked context (.put p) ⟨p.write context.slots lens (some shape), none⟩
  | copy {context p shape lens} (empty : context.temp = none)
      (found : p.find context.slots = some lens) (selected : lens.selected = some shape)
      (allowed : shape.copyable) :
      Checked context (.copy p) {context with temp := some shape}
  | drop {context shape} (resident : context.temp = some shape)
      (allowed : shape.disposable) (exhausted : shape.shallow) :
      Checked context .drop {context with temp := none}

/-- The authoritative local contract covers every depth, including whole slots.
It supplies actual progress, exact occupancy, and framed ownership together. -/
theorem Op.Checked.sound {n : Nat} {signature : Signature} {before after : Context n}
    {op : Op n} (checked : Op.Checked before op after) {state : State n}
    (typed : state.Typed signature before) :
    ∃ next, op.exec state = some next ∧ next.Typed signature after ∧ Conserves signature state next := by
  cases checked with
  | @take p mode input output lens empty found selected layout extract =>
    have unused : state.temp = none := by simpa [empty] using typed.2
    obtain ⟨actual, actualFound, actualTyped, rebuild⟩ := p.realized typed lens found
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (actualTyped.trans selected)
    obtain ⟨result, extracted, resultTyped, mass⟩ := extract.realized classified
    refine ⟨⟨p.write state.slots actual none, some result⟩,
      by simp [Op.exec, actualFound, live, extracted, unused],
      p.typed_write typed actual lens rebuild rfl (by simp [resultTyped]), ?_⟩
    have equal : ∀ identity, (State.mk (p.write state.slots actual none) (some result)).count identity =
        state.count identity := by
      intro identity
      have equation := p.count_write state actual actualFound none (some result) identity
      have same : weight identity (some result) = weight identity (some value) := mass identity
      rw [live, unused, same] at equation
      simp only [weight, cellMass] at equation
      omega
    exact ⟨fun i => by rw [equal i]; exact Nat.le_refl _, fun i _ => equal i⟩
  | @put p shape lens resident found fits =>
    obtain ⟨actual, actualFound, actualTyped, rebuild⟩ := p.realized typed lens found
    obtain ⟨available, absent⟩ := fits.realized actualTyped
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (typed.2.trans resident)
    refine ⟨⟨p.write state.slots actual (some value), none⟩,
      by simp [Op.exec, actualFound, live, available],
      p.typed_write typed actual lens rebuild (by simp [classified]) rfl, ?_⟩
    have equal : ∀ identity, (State.mk (p.write state.slots actual (some value)) none).count identity =
        state.count identity := by
      intro identity
      have equation := p.count_write state actual actualFound (some value) none identity
      rw [live, absent] at equation
      simp only [weight, cellMass] at equation
      omega
    exact ⟨fun i => by rw [equal i]; exact Nat.le_refl _, fun i _ => equal i⟩
  | @copy p shape lens empty found selected allowed =>
    have unused : state.temp = none := by simpa [empty] using typed.2
    obtain ⟨actual, actualFound, actualTyped, _⟩ := p.realized typed lens found
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (actualTyped.trans selected)
    have zero : ∀ identity, weight identity (some value) = 0 :=
      Value.copyable_zero (classified.symm ▸ allowed)
    refine ⟨{state with temp := some value}, by simp [Op.exec, actualFound, live, unused],
      ⟨typed.1, by simp [classified]⟩, ?_⟩
    exact ⟨fun i => by simp only [State.count]; rw [zero i, unused]; simp [weight, cellMass],
      fun i _ => by simp only [State.count]; rw [zero i, unused]; rfl⟩
  | @drop shape resident allowed exhausted =>
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (typed.2.trans resident)
    refine ⟨{state with temp := none}, by simp [Op.exec, live], ⟨typed.1, rfl⟩, ?_⟩
    refine ⟨fun _ => by simp [State.count, weight, cellMass], ?_⟩
    intro identity exactKind
    have absent : weight identity (some value) = 0 :=
      Value.disposable_exact_zero (classified.symm ▸ allowed) exactKind
    simp only [State.count, live]
    rw [absent]
    rfl

end OwnershipMir
