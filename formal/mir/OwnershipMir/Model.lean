import OwnershipMir.Focus

/-! A fixed-slot ownership region. Resource identity is independent of location;
its principal comes from one immutable signature, never a use-site annotation.
The ownership interpretation counts actual residents, including the transfer
register. It is not a second state maintained by the machine. -/
namespace OwnershipMir

def weight (identity : Nat) (cell : Option Value) : Nat :=
  cellMass (Atom.weight identity) (fun _ => 0) cell

def total : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => f 0 + total (fun i => f i.succ)

def update {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (a : α) : Fin n → α :=
  fun j => if j = i then a else f j

@[simp] theorem update_same {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (a : α) :
    update f i a i = a := by simp [update]

@[simp] theorem update_other {α : Type} {n : Nat} (f : Fin n → α) (i j : Fin n) (a : α)
    (different : j ≠ i) : update f i a j = f j := by simp [update, different]

theorem total_update {n : Nat} (f : Fin n → Nat) (i : Fin n) (a : Nat) :
    total (update f i a) + f i = total f + a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [total, update, Fin.ext_iff, Nat.add_left_comm, Nat.add_comm]
    · have tail := ih (fun k => f k.succ) j
      change total (fun k => if k = j then a else f k.succ) + f j.succ =
        total (fun k => f k.succ) + a at tail
      simpa [total, update, Fin.ext_iff, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg (fun x => f 0 + x) tail

structure State (n : Nat) where
  slots : Fin n → Option Value
  temp : Option Value

/-- Exact-occupancy checking policy: absence, holes, and live shells remain
distinct. This is a static abstraction of State, not another runtime state.
It intentionally does not admit maybe-initialized joins. -/
structure Context (n : Nat) where
  slots : Fin n → Option Shape
  temp : Option Shape

/-- Realization boundary. The checker demands one exact structural shape;
execution itself neither reads a Context nor relies on branch agreement. -/
def State.Typed {n : Nat} (signature : Signature) (state : State n) (context : Context n) : Prop :=
  (∀ i, (state.slots i).map (Value.kind signature) = context.slots i) ∧
  state.temp.map (Value.kind signature) = context.temp

def State.mass {n : Nat} (leaf : Atom → Nat) (shell : Shell → Nat) (state : State n) : Nat :=
  total (fun i => cellMass leaf shell (state.slots i)) + cellMass leaf shell state.temp

def State.count {n : Nat} (state : State n) (identity : Nat) : Nat :=
  total (fun i => weight identity (state.slots i)) + weight identity state.temp

def State.Unique {n : Nat} (state : State n) : Prop :=
  ∀ identity, state.count identity ≤ 1

/-- Exact resources are conserved, affine resources can only disappear.
Duplicable scalar data carries no resource identity. -/
structure Conserves {n : Nat} (signature : Signature) (before after : State n) : Prop where
  bounded : ∀ identity, after.count identity ≤ before.count identity
  exact : ∀ identity, signature identity = .exact → after.count identity = before.count identity

theorem Conserves.refl {n : Nat} (signature : Signature) (state : State n) :
    Conserves signature state state := ⟨fun _ => Nat.le_refl _, fun _ _ => rfl⟩

theorem Conserves.trans {n : Nat} {signature : Signature} {a b c : State n}
    (first : Conserves signature a b) (second : Conserves signature b c) :
    Conserves signature a c :=
  ⟨fun i => Nat.le_trans (second.bounded i) (first.bounded i),
    fun i exact => (second.exact i exact).trans (first.exact i exact)⟩

theorem Conserves.unique {n : Nat} {signature : Signature} {before after : State n}
    (conserved : Conserves signature before after) (unique : before.Unique) : after.Unique :=
  fun i => Nat.le_trans (conserved.bounded i) (unique i)

theorem typed_update {n : Nat} {signature : Signature} {state : State n} {context : Context n}
    (typed : state.Typed signature context) (i : Fin n) {value : Option Value} {kind : Option Shape}
    (resident : value.map (Value.kind signature) = kind) {temp : Option Value} {tempKind : Option Shape}
    (register : temp.map (Value.kind signature) = tempKind) :
    (State.mk (update state.slots i value) temp).Typed signature
      ⟨update context.slots i kind, tempKind⟩ := by
  refine ⟨fun j => ?_, register⟩
  by_cases same : j = i
  · subst j; simpa using resident
  · simpa [update, same] using typed.1 j

end OwnershipMir
