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

/-- Structural witnesses for the actual instruction transition. Permission
is separate: this relation also describes unchecked execution. -/
inductive Op.Effect {n : Nat} : Op n → State n → State n → Type where
  | take {state p mode lens value result}
      (found : p.find state.slots = some lens) (live : lens.selected = some value)
      (extracted : mode.apply value = some result) (empty : state.temp = none) :
      Effect (.take p mode) state ⟨p.write state.slots lens none, some result⟩
  | put {state p lens value} (found : p.find state.slots = some lens)
      (live : state.temp = some value) (available : vacant lens.selected = true) :
      Effect (.put p) state ⟨p.write state.slots lens (some value), none⟩
  | copy {state p lens value} (found : p.find state.slots = some lens)
      (live : lens.selected = some value) (empty : state.temp = none) :
      Effect (.copy p) state {state with temp := some value}
  | drop {state value} (live : state.temp = some value) :
      Effect .drop state {state with temp := none}

theorem Op.Effect.exec {n : Nat} {op : Op n} {before after : State n}
    (effect : op.Effect before after) : op.exec before = some after := by
  cases effect <;> simp_all [Op.exec]

noncomputable def Op.effect_of_exec {n : Nat} {op : Op n} {before after : State n}
    (executed : op.exec before = some after) : op.Effect before after := by
  cases op with
  | take p mode =>
    cases found : p.find before.slots <;> simp [Op.exec, found] at executed
    rename_i lens
    cases live : lens.selected <;> simp [live] at executed
    rename_i value
    cases extracted : mode.apply value <;> simp [extracted] at executed
    cases empty : before.temp <;> simp [empty] at executed
    cases executed
    exact .take found live extracted empty
  | put p =>
    cases found : p.find before.slots <;> simp [Op.exec, found] at executed
    rename_i lens
    cases live : before.temp <;> simp [live] at executed
    by_cases available : vacant lens.selected = true <;> simp [available] at executed
    cases executed
    exact .put found live available
  | copy p =>
    cases found : p.find before.slots <;> simp [Op.exec, found] at executed
    rename_i lens
    cases live : lens.selected <;> simp [live] at executed
    cases empty : before.temp <;> simp [empty] at executed
    cases executed
    exact .copy found live empty
  | drop =>
    cases live : before.temp <;> simp [Op.exec, live] at executed
    cases executed
    exact .drop live

/-- Only the resident capabilities needed for resource conservation, not full legality. -/
def Op.Effect.ConservationAllowed {n : Nat} {op : Op n} {before after : State n}
    (signature : Signature) : op.Effect before after → Prop
  | .take _ _ _ _ | .put _ _ _ => True
  | .copy (value := value) _ _ _ => (value.kind signature).copyable
  | .drop (value := value) _ => (value.kind signature).disposable

/-- Complete resident-level legality, derived only from the authoritative
checker. Execution witnesses already carry selection, vacancy and register facts. -/
def Op.Effect.Legal {n : Nat} {op : Op n} {before after : State n}
    (signature : Signature) : op.Effect before after → Prop
  | .take (p := p) (mode := mode) (value := value) (result := result) _ _ _ _ =>
      p.layout = (Value.kind signature value).layout id ∧ mode.Checked (Value.kind signature value) (Value.kind signature result)
  | .put (lens := lens) (value := value) _ _ _ =>
      Fits (Value.kind signature value) (lens.selected.map (Value.kind signature))
  | .copy (value := value) _ _ _ => (value.kind signature).copyable
  | .drop (value := value) _ => (value.kind signature).disposable ∧ (value.kind signature).shallow

theorem Op.Effect.Legal.conservationAllowed {n : Nat} {op : Op n} {before after : State n}
    {signature : Signature} {effect : op.Effect before after} (legal : effect.Legal signature) :
    effect.ConservationAllowed signature := by
  cases effect with
  | take => trivial
  | put => trivial
  | copy => exact legal
  | drop => exact legal.1

theorem vacant_mass_zero {cell : Cell Atom} (leaf : Atom → Nat) (shell : Shell → Nat)
    (empty : vacant cell = true) : cellMass leaf shell cell = 0 := by
  cases cell with
  | none => rfl
  | some tree => cases tree <;> simp [vacant] at empty <;> rfl

theorem Extract.resource_balance {mode : Extract} {value result : Value}
    (executed : mode.apply value = some result) (identity : Nat) :
    resourceMass identity result = resourceMass identity value := by
  cases mode with
  | whole => cases Option.some.inj executed; rfl
  | deconstruct =>
    cases value <;> simp only [Extract.apply, Option.some.injEq] at executed
    all_goals try contradiction
    subst result
    simp [resourceMass, Tree.mass]

/-- Ownership observations consume the transition witness, not a second
reconstruction of selection and execution from typing. -/
theorem Op.Effect.conserves {n : Nat} {op : Op n} {state next : State n}
    {signature : Signature} (effect : op.Effect state next) (allowed : effect.ConservationAllowed signature) :
    Conserves signature state next := by
  cases effect with
  | @take _ p mode actual value result found live extracted unused =>
    have equal : ∀ identity, (State.mk (p.write state.slots actual none) (some result)).count identity =
        state.count identity := by
      intro identity
      have equation := p.count_write state actual found none (some result) identity
      have same : weight identity (some result) = weight identity (some value) := Extract.resource_balance extracted identity
      rw [live, unused, same] at equation
      simp only [weight, cellMass] at equation
      omega
    exact ⟨fun i => by rw [equal i]; exact Nat.le_refl _, fun i _ => equal i⟩
  | @put _ p actual value found live available =>
    have equal : ∀ identity, (State.mk (p.write state.slots actual (some value)) none).count identity =
        state.count identity := by
      intro identity
      have equation := p.count_write state actual found (some value) none identity
      have absent : weight identity actual.selected = 0 := vacant_mass_zero _ _ available
      rw [live, absent] at equation
      simp only [weight, cellMass] at equation
      omega
    exact ⟨fun i => by rw [equal i]; exact Nat.le_refl _, fun i _ => equal i⟩
  | @copy _ p actual value found live unused =>
    have zero : ∀ identity, weight identity (some value) = 0 := Value.copyable_zero allowed
    exact ⟨fun i => by simp only [State.count]; rw [zero i, unused]; simp [weight, cellMass],
      fun i _ => by simp only [State.count]; rw [zero i, unused]; rfl⟩
  | @drop _ value live =>
    refine ⟨fun _ => by simp [State.count, weight, cellMass], ?_⟩
    intro identity exactKind
    have absent : weight identity (some value) = 0 := Value.disposable_exact_zero allowed exactKind
    simp only [State.count, live]
    rw [absent]
    rfl

/-- Checking constructs the structural transition once and derives its
realization and resident capabilities. No post-state property is an input. -/
theorem Op.Checked.realize {n : Nat} {signature : Signature} {before after : Context n}
    {op : Op n} (checked : Op.Checked before op after) {state : State n}
    (typed : state.Typed signature before) :
    ∃ next, ∃ effect : op.Effect state next, next.Typed signature after ∧ effect.Legal signature := by
  cases checked with
  | @take p mode input output lens empty found selected layout extract =>
    have unused : state.temp = none := by simpa [empty] using typed.2
    obtain ⟨actual, actualFound, actualTyped, rebuild⟩ := p.realized typed lens found
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (actualTyped.trans selected)
    obtain ⟨result, extracted, resultTyped⟩ := extract.realized classified
    exact ⟨_, .take actualFound live extracted unused,
      p.typed_write typed actual lens rebuild rfl (by simp [resultTyped]), by
        change p.layout = (value.kind signature).layout id ∧ mode.Checked (value.kind signature) (result.kind signature)
        rw [classified, resultTyped]
        exact ⟨layout, extract⟩⟩
  | @put p shape lens resident found fits =>
    obtain ⟨actual, actualFound, actualTyped, rebuild⟩ := p.realized typed lens found
    obtain ⟨available, _⟩ := fits.realized actualTyped
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (typed.2.trans resident)
    exact ⟨_, .put actualFound live available,
      p.typed_write typed actual lens rebuild (by simp [classified]) rfl, by
        change Fits (value.kind signature) (actual.selected.map (Value.kind signature))
        rw [classified, actualTyped]
        exact fits⟩
  | @copy p shape lens empty found selected allowed =>
    have unused : state.temp = none := by simpa [empty] using typed.2
    obtain ⟨actual, actualFound, actualTyped, _⟩ := p.realized typed lens found
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (actualTyped.trans selected)
    exact ⟨_, .copy actualFound live unused, ⟨typed.1, by simp [classified]⟩, by
      change (value.kind signature).copyable
      exact classified.symm ▸ allowed⟩
  | @drop shape resident allowed exhausted =>
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (typed.2.trans resident)
    exact ⟨_, .drop live, ⟨typed.1, rfl⟩, by
      change (value.kind signature).disposable ∧ (value.kind signature).shallow
      rw [classified]
      exact ⟨allowed, exhausted⟩⟩

theorem Op.Checked.effect {n : Nat} {signature : Signature} {before after : Context n}
    {op : Op n} (checked : Op.Checked before op after) {state next : State n}
    (typed : state.Typed signature before) (executed : op.exec state = some next) :
    ∃ effect : op.Effect state next, next.Typed signature after ∧ effect.Legal signature := by
  obtain ⟨result, effect, realized, allowed⟩ := checked.realize typed
  cases Option.some.inj (executed.symm.trans effect.exec)
  exact ⟨effect, realized, allowed⟩

theorem Op.Checked.sound {n : Nat} {signature : Signature} {before after : Context n}
    {op : Op n} (checked : Op.Checked before op after) {state : State n}
    (typed : state.Typed signature before) :
    ∃ next, op.exec state = some next ∧ next.Typed signature after ∧ Conserves signature state next := by
  obtain ⟨next, effect, realized, allowed⟩ := checked.realize typed
  exact ⟨next, effect.exec, realized, effect.conserves allowed.conservationAllowed⟩

end OwnershipMir
