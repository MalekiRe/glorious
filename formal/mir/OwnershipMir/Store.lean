import OwnershipMir.Model

namespace OwnershipMir

abbrev Region (n : Nat) (α : Type) := Fin n → Cell α

/-- Region identities are never reused. A retired region is absent, not an
empty live region. Only the machine's one transfer register is outside regions. -/
structure Store (n : Nat) (α : Type) where
  regions : List (Option (Region n α))
  temp : Cell α

namespace Store

def region {n : Nat} {α : Type} (store : Store n α) (identity : Nat) : Option (Region n α) :=
  (store.regions[identity]?).join

def replace {n : Nat} {α : Type} (store : Store n α) (identity : Nat)
    (slots : Region n α) (temp : Cell α) : Store n α :=
  ⟨store.regions.set identity (some slots), temp⟩

def allocate {n : Nat} {α : Type} (store : Store n α) (slots : Region n α) : Store n α :=
  ⟨store.regions ++ [some slots], none⟩

def retire {n : Nat} {α : Type} (store : Store n α) (identity : Nat) : Store n α :=
  ⟨store.regions.set identity none, store.temp⟩

theorem region_bound {n : Nat} {α : Type} {store : Store n α} {identity : Nat} {slots : Region n α}
    (live : store.region identity = some slots) : identity < store.regions.length := by
  by_cases bound : identity < store.regions.length
  · exact bound
  · have absent := List.getElem?_eq_none (l := store.regions) (Nat.not_lt.mp bound)
    simp [region, absent] at live

theorem replace_same {n : Nat} {α : Type} {store : Store n α} {identity : Nat}
    (bound : identity < store.regions.length) (slots : Region n α) (temp : Cell α) :
    (store.replace identity slots temp).region identity = some slots := by
  simp [replace, region, bound]

theorem replace_other {n : Nat} {α : Type} (store : Store n α) (identity other : Nat)
    (slots : Region n α) (temp : Cell α) (different : other ≠ identity) :
    (store.replace identity slots temp).region other = store.region other := by
  simp [replace, region, Ne.symm different]

theorem allocate_fresh {n : Nat} {α : Type} (store : Store n α) (slots : Region n α) :
    (store.allocate slots).region store.regions.length = some slots := by
  simp [allocate, region]

theorem allocate_old {n : Nat} {α : Type} {store : Store n α} {identity : Nat}
    (bound : identity < store.regions.length) (slots : Region n α) :
    (store.allocate slots).region identity = store.region identity := by
  simp [allocate, region, List.getElem?_append_left bound]

theorem retire_same {n : Nat} {α : Type} (store : Store n α) (identity : Nat) :
    (store.retire identity).region identity = none := by
  by_cases bound : identity < store.regions.length
  · simp [retire, region, bound]
  · have absent := List.getElem?_eq_none (l := store.regions) (Nat.not_lt.mp bound)
    simp [retire, region, List.set_eq_of_length_le (Nat.not_lt.mp bound), absent]

theorem retire_other {n : Nat} {α : Type} (store : Store n α) (identity other : Nat)
    (different : other ≠ identity) :
    (store.retire identity).region other = store.region other := by
  simp [retire, region, Ne.symm different]

/-- Each measure counts the one physical store, independently of its control stack. -/
def mass {n : Nat} {α : Type} (store : Store n α) (leaf : α → Nat) (shell : Shell → Nat) : Nat :=
  (store.regions.map (fun region => match region with
    | none => 0
    | some slots => total (fun i => cellMass leaf shell (slots i)))).sum + cellMass leaf shell store.temp

private theorem sum_set {α : Type} (measure : α → Nat) (items : List α) (index : Nat)
    (old value : α) (found : items[index]? = some old) :
    ((items.set index value).map measure).sum + measure old =
      (items.map measure).sum + measure value := by
  induction items generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp at found; subst old; simp [Nat.add_comm, Nat.add_left_comm]
    | succ index =>
      have rest := ih index (by simpa using found)
      simpa [List.set, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg (measure head + ·) rest

theorem replace_mass {n : Nat} {α : Type} (store : Store n α) {identity : Nat} {old : Region n α}
    (live : store.region identity = some old) (slots : Region n α) (temp : Cell α)
    (leaf : α → Nat) (shell : Shell → Nat) :
    (store.replace identity slots temp).mass leaf shell +
      total (fun i => cellMass leaf shell (old i)) + cellMass leaf shell store.temp =
    store.mass leaf shell + total (fun i => cellMass leaf shell (slots i)) + cellMass leaf shell temp := by
  have found : store.regions[identity]? = some (some old) := by
    cases h : store.regions[identity]? <;> simp [region, h] at live
    rename_i value
    cases value <;> simp_all
  have equation := sum_set (fun region : Option (Region n α) => match region with
    | none => 0 | some slots => total (fun i => cellMass leaf shell (slots i)))
    store.regions identity (some old) (some slots) found
  simp only [replace, mass] at *
  omega

theorem allocate_mass {n : Nat} {α : Type} (store : Store n α) (slots : Region n α)
    (leaf : α → Nat) (shell : Shell → Nat) :
    (store.allocate slots).mass leaf shell + cellMass leaf shell store.temp =
      store.mass leaf shell + total (fun i => cellMass leaf shell (slots i)) := by
  simp [allocate, mass, cellMass, Nat.add_comm, Nat.add_left_comm]

theorem retire_mass {n : Nat} {α : Type} (store : Store n α) {identity : Nat} {old : Region n α}
    (live : store.region identity = some old) (leaf : α → Nat) (shell : Shell → Nat) :
    (store.retire identity).mass leaf shell + total (fun i => cellMass leaf shell (old i)) =
      store.mass leaf shell := by
  have found : store.regions[identity]? = some (some old) := by
    cases h : store.regions[identity]? <;> simp [region, h] at live
    rename_i value
    cases value <;> simp_all
  have equation := sum_set (fun region : Option (Region n α) => match region with
    | none => 0 | some slots => total (fun i => cellMass leaf shell (slots i)))
    store.regions identity (some old) none found
  simp only [retire, mass] at *
  omega

theorem replace_self {n : Nat} {α : Type} {store : Store n α} {identity : Nat} {slots : Region n α}
    (live : store.region identity = some slots) : store.replace identity slots store.temp = store := by
  have same : ∀ (items : List (Option (Region n α))) (index : Nat),
      items[index]?.join = some slots → items.set index (some slots) = items := by
    intro items
    induction items with
    | nil => intro index found; simp at found
    | cons head tail ih =>
      intro index found
      cases index with
      | zero => simp at found; subst head; rfl
      | succ index => exact congrArg (head :: ·) (ih index (by simpa using found))
  cases store with
  | mk regions temp => exact congrArg (fun regions => Store.mk regions temp) (same regions identity live)

@[simp] theorem replace_replace {n : Nat} {α : Type} (store : Store n α) (identity : Nat)
    (first last : Region n α) (temp next : Cell α) :
    (store.replace identity first temp).replace identity last next = store.replace identity last next := by
  simp [replace, List.set_set]

@[simp] theorem retire_replace {n : Nat} {α : Type} (store : Store n α) (identity : Nat)
    (slots : Region n α) (temp : Cell α) :
    (store.replace identity slots temp).retire identity = {store.retire identity with temp := temp} := by
  simp [replace, retire, List.set_set]


theorem replace_mass_state {n : Nat} {store : Store n Atom} {identity : Nat}
    {slots : Region n Atom} (live : store.region identity = some slots) (next : State n)
    (leaf : Atom → Nat) (shell : Shell → Nat) :
    (store.replace identity next.slots next.temp).mass leaf shell + (State.mk slots store.temp).mass leaf shell =
      store.mass leaf shell + next.mass leaf shell := by
  have equation := store.replace_mass live next.slots next.temp leaf shell
  simp only [State.mass]
  omega


end Store
end OwnershipMir
