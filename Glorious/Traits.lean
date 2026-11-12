/-!
# Which implementation a trait bound is met by

A trait is a set of functions a type may have. `impl Trait for Head<T, ...>`
gives them for every type made with `Head`, perhaps on condition that some of
the `T` have traits themselves. A use of one of the functions at a type needs
the implementation for that type, and that is found here, by a function the
checker of the source text calls.

Two things are proved of it. What the function finds is evidence that the bound
is met: `solve_sound`. And a bound is met in at most one way, if no two
implementations are for the same trait and the same head and what a function
may assume of its own type parameters is not said twice: `coherent`. So which
implementation runs does not depend on how it was looked for.

Nothing here knows what a program means. The elaborator turns evidence into a
value, a tuple of the implementation's functions, and passes it where the bound
is needed; that the result is well typed is checked for each program, with the
rest of its Core.
-/

namespace Glorious.Traits

/-- A type as far as finding an implementation is concerned: one made with a
name, or one the function being checked is generic in. -/
inductive STy where
  | con (name : String) (args : List STy)
  | var (id : Nat)

/-- `impl Trait for Head<T0, ..., Tn>`, on condition that each `(trait, i)` in
`context` holds: that `Ti` has that trait. -/
structure Impl where
  trait : String
  head : String
  arity : Nat
  context : List (String × Nat)

/-- How a bound is met: by an implementation, given how each of its conditions
is met, or by something the function being checked assumes. -/
inductive Dict where
  | impl (i : Nat) (subs : List Dict)
  | given (k : Nat)

/-- What a function assumes of its own type parameters: each a trait and a type
variable. -/
abbrev Givens := List (String × Nat)

mutual

/-- `tr` holds of a type, and this is how. -/
inductive Entails (impls : List Impl) (givens : Givens) : String → STy → Dict → Prop where
  | given {k : Nat} {tr : String} {v : Nat} :
      givens[k]? = some (tr, v) → Entails impls givens tr (.var v) (.given k)
  | impl {i : Nat} {I : Impl} {tr head : String} {args : List STy} {subs : List Dict} :
      impls[i]? = some I → I.trait = tr → I.head = head → I.arity = args.length →
      EntailsAll impls givens I.context args subs →
      Entails impls givens tr (.con head args) (.impl i subs)

/-- Each condition of an implementation holds of the argument it is about. -/
inductive EntailsAll (impls : List Impl) (givens : Givens) :
    List (String × Nat) → List STy → List Dict → Prop where
  | nil {args : List STy} : EntailsAll impls givens [] args []
  | cons {tr : String} {j : Nat} {ctx : List (String × Nat)} {args : List STy} {τ : STy}
      {d : Dict} {ds : List Dict} :
      args[j]? = some τ → Entails impls givens tr τ d → EntailsAll impls givens ctx args ds →
      EntailsAll impls givens ((tr, j) :: ctx) args (d :: ds)

end

/-! ## Finding it -/

/-- The first implementation of `tr` for `head` at this arity, with its place. -/
def findImpl (tr head : String) (n : Nat) : List Impl → Option (Nat × Impl)
  | [] => none
  | I :: rest =>
    if I.trait = tr ∧ I.head = head ∧ I.arity = n then some (0, I)
    else (findImpl tr head n rest).map fun x => (x.1 + 1, x.2)

theorem findImpl_sound {tr head : String} {n : Nat} : ∀ {impls : List Impl} {i : Nat} {I : Impl},
    findImpl tr head n impls = some (i, I) →
    impls[i]? = some I ∧ I.trait = tr ∧ I.head = head ∧ I.arity = n
  | [], _, _, h => by simp [findImpl] at h
  | J :: rest, i, I, h => by
    simp only [findImpl] at h
    split at h
    · rename_i hJ
      cases h
      exact ⟨rfl, hJ⟩
    · cases hr : findImpl tr head n rest with
      | none => simp [hr] at h
      | some x =>
        obtain ⟨i', I'⟩ := x
        simp [hr] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := findImpl_sound hr
        exact ⟨by simpa using h1, h2⟩

/-- Where an assumption is among those a function makes. -/
def findGiven (tr : String) (v : Nat) : Givens → Option Nat
  | [] => none
  | g :: rest => if g = (tr, v) then some 0 else (findGiven tr v rest).map (· + 1)

theorem findGiven_sound {tr : String} {v : Nat} : ∀ {givens : Givens} {k : Nat},
    findGiven tr v givens = some k → givens[k]? = some (tr, v)
  | [], _, h => by simp [findGiven] at h
  | g :: rest, k, h => by
    simp only [findGiven] at h
    split at h
    · rename_i hg
      cases h
      simp [hg]
    · cases hr : findGiven tr v rest with
      | none => simp [hr] at h
      | some k' =>
        simp [hr] at h
        subst h
        simpa using findGiven_sound hr

/-- Meet each condition of an implementation, given how to meet a bound. -/
def collect (f : String → STy → Option Dict) (args : List STy) :
    List (String × Nat) → Option (List Dict)
  | [] => some []
  | (tr, j) :: ctx =>
    match args[j]? with
    | none => none
    | some τ =>
      match f tr τ, collect f args ctx with
      | some d, some ds => some (d :: ds)
      | _, _ => none

/-- How `tr` holds of a type, if it can be found within `fuel` implementations
one inside another. A type variable has a trait only if that is assumed. -/
def solve (impls : List Impl) (givens : Givens) : Nat → String → STy → Option Dict
  | 0, _, _ => none
  | _ + 1, tr, .var v => (findGiven tr v givens).map .given
  | fuel + 1, tr, .con head args =>
    match findImpl tr head args.length impls with
    | none => none
    | some (i, I) => (collect (solve impls givens fuel) args I.context).map (.impl i)

theorem collect_sound {impls : List Impl} {givens : Givens} {f : String → STy → Option Dict}
    (hf : ∀ tr τ d, f tr τ = some d → Entails impls givens tr τ d) {args : List STy} :
    ∀ {ctx : List (String × Nat)} {ds : List Dict}, collect f args ctx = some ds →
      EntailsAll impls givens ctx args ds
  | [], _, h => by
    simp only [collect, Option.some.injEq] at h
    subst h
    exact .nil
  | (tr, j) :: ctx, ds, h => by
    simp only [collect] at h
    split at h
    · cases h
    · rename_i τ hτ
      split at h
      · rename_i d ds' hd hds
        cases h
        exact .cons hτ (hf tr τ d hd) (collect_sound hf hds)
      · cases h

/-- **What is found is evidence.** -/
theorem solve_sound {impls : List Impl} {givens : Givens} : ∀ (fuel : Nat) {tr : String}
    {τ : STy} {d : Dict}, solve impls givens fuel tr τ = some d → Entails impls givens tr τ d
  | 0, _, _, _, h => by simp [solve] at h
  | fuel + 1, tr, .var v, d, h => by
    simp only [solve] at h
    cases hk : findGiven tr v givens with
    | none => simp [hk] at h
    | some k =>
      simp [hk] at h
      subst h
      exact .given (findGiven_sound hk)
  | fuel + 1, tr, .con head args, d, h => by
    simp only [solve] at h
    split at h
    · cases h
    · rename_i i I hfind
      obtain ⟨hi, htr, hhead, harity⟩ := findImpl_sound hfind
      cases hc : collect (solve impls givens fuel) args I.context with
      | none => simp [hc] at h
      | some ds =>
        simp [hc] at h
        subst h
        exact .impl hi htr hhead harity
          (collect_sound (fun _ _ _ hd => solve_sound fuel hd) hc)

/-! ## At most one way -/

/-- No two implementations are for the same trait and the same head. -/
def NoOverlap (impls : List Impl) : Prop :=
  ∀ (i j : Nat) (I J : Impl), impls[i]? = some I → impls[j]? = some J → I.trait = J.trait →
    I.head = J.head → I.arity = J.arity → i = j

/-- Nothing is assumed twice. -/
def Distinct (givens : Givens) : Prop :=
  ∀ (k l : Nat) (x : String × Nat), givens[k]? = some x → givens[l]? = some x → k = l

mutual

/-- **A bound is met in at most one way.** -/
theorem coherent {impls : List Impl} {givens : Givens} (hn : NoOverlap impls)
    (hg : Distinct givens) : ∀ {tr : String} {τ : STy} {d d' : Dict},
    Entails impls givens tr τ d → Entails impls givens tr τ d' → d = d'
  | _, _, _, _, .given h, h' => by
    cases h' with
    | given h2 => rw [hg _ _ _ h h2]
  | _, _, _, _, .impl hi ht hh ha hall, h' => by
    cases h' with
    | impl hj ht' hh' ha' hall' =>
      have e := hn _ _ _ _ hi hj (ht.trans ht'.symm) (hh.trans hh'.symm) (ha.trans ha'.symm)
      subst e
      rw [hi] at hj
      cases hj
      rw [coherentAll hn hg hall hall']

theorem coherentAll {impls : List Impl} {givens : Givens} (hn : NoOverlap impls)
    (hg : Distinct givens) : ∀ {ctx : List (String × Nat)} {args : List STy} {ds ds' : List Dict},
    EntailsAll impls givens ctx args ds → EntailsAll impls givens ctx args ds' → ds = ds'
  | _, _, _, _, .nil, h' => by
    cases h'
    rfl
  | _, _, _, _, .cons hτ hd hrest, h' => by
    cases h' with
    | cons hτ' hd' hrest' =>
      rw [hτ] at hτ'
      cases hτ'
      rw [coherent hn hg hd hd', coherentAll hn hg hrest hrest']

end

/-! ## Checking the conditions -/

/-- Is no implementation for the same trait and head as a later one? -/
def noOverlap : List Impl → Bool
  | [] => true
  | I :: rest =>
    rest.all (fun J => !(I.trait == J.trait && I.head == J.head && I.arity == J.arity))
      && noOverlap rest

theorem noOverlap_sound : ∀ {impls : List Impl}, noOverlap impls = true → NoOverlap impls
  | [], _ => fun i _ _ _ hi => by simp at hi
  | I₀ :: rest, h => by
    simp only [noOverlap, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨hhead, hrest⟩ := h
    have ih := noOverlap_sound hrest
    have hne : ∀ J, J ∈ rest → I₀.trait = J.trait → I₀.head = J.head → I₀.arity = J.arity →
        False := by
      intro J hJ h1 h2 h3
      rcases hhead J hJ with (h | h) | h
      · exact h h1
      · exact h h2
      · exact h h3
    intro i j I J hi hj ht hh ha
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp at hi
        subst hi
        exact (hne J (List.mem_of_getElem? (by simpa using hj)) ht hh ha).elim
    | succ i =>
      cases j with
      | zero =>
        simp at hj
        subst hj
        exact (hne I (List.mem_of_getElem? (by simpa using hi)) ht.symm hh.symm ha.symm).elim
      | succ j =>
        have := ih i j I J (by simpa using hi) (by simpa using hj) ht hh ha
        rw [this]

/-- Is nothing assumed twice? -/
def distinct : Givens → Bool
  | [] => true
  | g :: rest => !rest.contains g && distinct rest

theorem distinct_sound : ∀ {givens : Givens}, distinct givens = true → Distinct givens
  | [], _ => fun k _ _ hk => by simp at hk
  | g :: rest, h => by
    simp only [distinct, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    obtain ⟨hg, hrest⟩ := h
    have ih := distinct_sound hrest
    intro k l x hk hl
    cases k with
    | zero =>
      cases l with
      | zero => rfl
      | succ l =>
        simp at hk
        subst hk
        exact absurd (List.mem_of_getElem? (by simpa using hl)) hg
    | succ k =>
      cases l with
      | zero =>
        simp at hl
        subst hl
        exact absurd (List.mem_of_getElem? (by simpa using hk)) hg
      | succ l =>
        have := ih k l x (by simpa using hk) (by simpa using hl)
        rw [this]

/--
**What the checker uses.** Where the implementations and the assumptions pass
the two checks, what `solve` finds is evidence that the bound is met, and any
evidence that it is met is that same evidence.
-/
theorem solve_unique {impls : List Impl} {givens : Givens} (hn : noOverlap impls = true)
    (hg : distinct givens = true) {fuel : Nat} {tr : String} {τ : STy} {d d' : Dict}
    (h : solve impls givens fuel tr τ = some d) (h' : Entails impls givens tr τ d') : d' = d :=
  coherent (noOverlap_sound hn) (distinct_sound hg) h' (solve_sound fuel h)

end Glorious.Traits
