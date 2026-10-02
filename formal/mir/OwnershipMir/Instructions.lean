import OwnershipMir.Model

namespace OwnershipMir

inductive Op (n : Nat) where
  | take (slot : Fin n)
  | put (slot : Fin n)
  | copy (slot : Fin n)
  | drop

/-- Raw execution does not consult typing or permissions. In particular an
unchecked copy or drop can violate ownership; admission must rule that out. -/
def Op.exec {n : Nat} : Op n → State n → Option (State n)
  | .take i, state => match state.temp, state.slots i with
    | none, some value => some ⟨update state.slots i none, some value⟩
    | _, _ => none
  | .put i, state => match state.temp, state.slots i with
    | some value, none => some ⟨update state.slots i (some value), none⟩
    | _, _ => none
  | .copy i, state => match state.temp, state.slots i with
    | none, some value => some { state with temp := some value }
    | _, _ => none
  | .drop, state => match state.temp with
    | some _ => some { state with temp := none }
    | none => none

inductive Op.Checked {n : Nat} : Context n → Op n → Context n → Prop where
  | take {context i kind} (empty : context.temp = none) (found : context.slots i = some kind) :
      Checked context (.take i) ⟨update context.slots i none, some kind⟩
  | put {context i kind} (resident : context.temp = some kind) (vacant : context.slots i = none) :
      Checked context (.put i) ⟨update context.slots i (some kind), none⟩
  | copy {context i} (empty : context.temp = none) (found : context.slots i = some .data) :
      Checked context (.copy i) { context with temp := some .data }
  | drop {context kind} (resident : context.temp = some kind) (allowed : kind ≠ .exact) :
      Checked context .drop { context with temp := none }

/-- One local producer supplies progress, realization, and the resource
interpretation for the actual operation, including its transient register. -/
theorem Op.Checked.sound {n : Nat} {signature : Signature} {before after : Context n}
    {op : Op n} (checked : Op.Checked before op after) {state : State n}
    (typed : state.Typed signature before) :
    ∃ next, op.exec state = some next ∧ next.Typed signature after ∧ Conserves signature state next := by
  cases checked with
  | @take i kind empty found =>
    have unused : state.temp = none := by simpa [empty] using typed.2
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp ((typed.1 i).trans found)
    refine ⟨⟨update state.slots i none, some value⟩, by simp [Op.exec, unused, live],
      typed_update typed i rfl (by simp [classified]), ?_⟩
    have equal : ∀ identity, (State.mk (update state.slots i none) (some value)).count identity =
        state.count identity := by
      intro identity
      have changed := weight_update state.slots i none identity
      simpa [State.count, live, unused, weight] using changed
    exact ⟨fun i => by rw [equal i]; exact Nat.le_refl _, fun i _ => equal i⟩
  | @put i kind resident vacant =>
    have empty : state.slots i = none := by simpa [vacant] using typed.1 i
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (typed.2.trans resident)
    refine ⟨⟨update state.slots i (some value), none⟩, by simp [Op.exec, live, empty],
      typed_update typed i (by simp [classified]) rfl, ?_⟩
    have equal : ∀ identity, (State.mk (update state.slots i (some value)) none).count identity =
        state.count identity := by
      intro identity
      have changed := weight_update state.slots i (some value) identity
      simpa [State.count, live, empty, weight] using changed
    exact ⟨fun i => by rw [equal i]; exact Nat.le_refl _, fun i _ => equal i⟩
  | @copy i empty found =>
    have unused : state.temp = none := by simpa [empty] using typed.2
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp ((typed.1 i).trans found)
    have scalar : ∃ payload, value = .data payload := by
      cases value with
      | data payload => exact ⟨payload, rfl⟩
      | owner identity => cases h : signature identity <;> simp [Value.kind, h, LinearKind.kind] at classified
    obtain ⟨payload, rfl⟩ := scalar
    refine ⟨{state with temp := some (.data payload)}, by simp [Op.exec, unused, live],
      ⟨typed.1, rfl⟩, ?_⟩
    exact ⟨fun _ => by simp [State.count, unused, weight], fun _ _ => by simp [State.count, unused, weight]⟩
  | @drop kind resident allowed =>
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (typed.2.trans resident)
    refine ⟨{state with temp := none}, by simp [Op.exec, live], ⟨typed.1, rfl⟩, ?_⟩
    refine ⟨fun _ => by simp [State.count, weight], ?_⟩
    intro identity exactKind
    have absent : weight identity (some value) = 0 := by
      cases value with
      | data payload => rfl
      | owner other =>
        by_cases same : identity = other
        · subst other; simp [Value.kind, exactKind, LinearKind.kind] at classified
          exact False.elim (allowed classified.symm)
        · simp [weight, same]
    simp only [State.count, live]
    rw [absent]
    rfl

end OwnershipMir
