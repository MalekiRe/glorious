import Std

/-! A fixed-slot ownership region. Resource identity is independent of location;
its principal comes from one immutable signature, never a use-site annotation.
The ownership interpretation counts actual residents, including the transfer
register. It is not a second state maintained by the machine. -/
namespace OwnershipMir

inductive LinearKind where
  | affine | exact
  deriving DecidableEq

inductive Kind where
  | data | affine | exact
  deriving DecidableEq

def LinearKind.kind : LinearKind → Kind
  | .affine => .affine
  | .exact => .exact

abbrev Signature := Nat → LinearKind

inductive Value where
  | data (payload : Nat)
  | owner (identity : Nat)
  deriving DecidableEq

def Value.kind (signature : Signature) : Value → Kind
  | .data _ => .data
  | .owner identity => (signature identity).kind

def weight (identity : Nat) : Option Value → Nat
  | some (.owner other) => if identity = other then 1 else 0
  | _ => 0

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

structure Context (n : Nat) where
  slots : Fin n → Option Kind
  temp : Option Kind

def State.Typed {n : Nat} (signature : Signature) (state : State n) (context : Context n) : Prop :=
  (∀ i, (state.slots i).map (Value.kind signature) = context.slots i) ∧
  state.temp.map (Value.kind signature) = context.temp

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

theorem weight_update {n : Nat} (slots : Fin n → Option Value) (i : Fin n)
    (value : Option Value) (identity : Nat) :
    total (fun j => weight identity (update slots i value j)) + weight identity (slots i) =
      total (fun j => weight identity (slots j)) + weight identity value := by
  have pointwise : (fun j => weight identity (update slots i value j)) =
      update (fun j => weight identity (slots j)) i (weight identity value) := by
    funext j; simp only [update]; split <;> rfl
  rw [pointwise]
  exact total_update _ _ _

theorem typed_update {n : Nat} {signature : Signature} {state : State n} {context : Context n}
    (typed : state.Typed signature context) (i : Fin n) {value : Option Value} {kind : Option Kind}
    (resident : value.map (Value.kind signature) = kind) {temp : Option Value} {tempKind : Option Kind}
    (register : temp.map (Value.kind signature) = tempKind) :
    (State.mk (update state.slots i value) temp).Typed signature
      ⟨update context.slots i kind, tempKind⟩ := by
  refine ⟨fun j => ?_, register⟩
  by_cases same : j = i
  · subst j; simpa using resident
  · simpa [update, same] using typed.1 j

end OwnershipMir
