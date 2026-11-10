import Glorious.Typing.Checker

/-!
# Clauses that cover every argument

A check that the clauses of a function leave no typed argument list unmatched,
and its proof. This discharges the one assumption `ProgramOk` makes beyond
typing. The check is the usual one: look at the first column; either the rows
that match anything there cover the rest, or every constructor of the column's
type is covered once its fields are put in front.
-/

namespace Glorious.Typing

open Core

variable {C : Cert}

/-- Does the pattern match every value? -/
def irrefutable : Pat → Bool
  | .wild => true
  | .bind => true
  | .int _ => false
  | .ctor _ _ => false

def headIsCtor : List Pat → Bool
  | .ctor _ _ :: _ => true
  | _ => false

/-- The rows whose first pattern matches anything, without that pattern. -/
def defaults : List (List Pat) → List (List Pat)
  | [] => []
  | [] :: rows => defaults rows
  | (p :: ps) :: rows => if irrefutable p then ps :: defaults rows else defaults rows

/-- The rows that can match a value built by `tag` with `n` fields, with
patterns for the fields in place of the first pattern. -/
def specialize (tag n : Nat) : List (List Pat) → List (List Pat)
  | [] => []
  | [] :: rows => specialize tag n rows
  | (p :: ps) :: rows =>
    match p with
    | .wild => (List.replicate n .wild ++ ps) :: specialize tag n rows
    | .bind => (List.replicate n .wild ++ ps) :: specialize tag n rows
    | .int _ => specialize tag n rows
    | .ctor t qs =>
      if t = tag ∧ qs.length = n then (qs ++ ps) :: specialize tag n rows
      else specialize tag n rows

/-- Every constructor of a type, with its field types. -/
def ctorsOf (C : Cert) : Ty → Option (List (Nat × List Ty))
  | .tuple Fs => some [(0, Fs)]
  | .data name args => findData C.datas name args
  | .int => none
  | .fn _ _ _ => none
  | .ref _ => none

/-- Do the rows cover every list of values of these types? `fuel` bounds the
depth of the search; running out means no. -/
def covers (C : Cert) : Nat → List (List Pat) → List Ty → Bool
  | 0, _, _ => false
  | _ + 1, rows, [] => rows.any List.isEmpty
  | fuel + 1, rows, T :: Ts =>
    !rows.isEmpty
      && (covers C fuel (defaults rows) Ts
        || (rows.any headIsCtor
          && (match ctorsOf C T with
              | some ctors =>
                ctors.all fun c => covers C fuel (specialize c.1 c.2.length rows) (c.2 ++ Ts)
              | none => false)))

/-! ## What the pieces mean -/

theorem irrefutable_match {p : Pat} (h : irrefutable p = true) (v : Value) :
    ∃ b, p.matchVal v = some b := by
  cases p with
  | wild => exact ⟨[], by simp [Pat.matchVal]⟩
  | bind => exact ⟨[v], by simp [Pat.matchVal]⟩
  | int n => simp [irrefutable] at h
  | ctor t qs => simp [irrefutable] at h

theorem defaults_mem : ∀ {rows : List (List Pat)} {ps : List Pat}, ps ∈ defaults rows →
    ∃ p, irrefutable p = true ∧ (p :: ps) ∈ rows
  | [], _, h => by simp [defaults] at h
  | [] :: rows, ps, h => by
    simp only [defaults] at h
    obtain ⟨p, hp, hm⟩ := defaults_mem h
    exact ⟨p, hp, List.mem_cons_of_mem _ hm⟩
  | (p :: ps') :: rows, ps, h => by
    simp only [defaults] at h
    split at h
    · rename_i hp
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨p, hp, List.mem_cons_self ..⟩
      · obtain ⟨q, hq, hm⟩ := defaults_mem h
        exact ⟨q, hq, List.mem_cons_of_mem _ hm⟩
    · obtain ⟨q, hq, hm⟩ := defaults_mem h
      exact ⟨q, hq, List.mem_cons_of_mem _ hm⟩

theorem specialize_mem {tag n : Nat} : ∀ {rows : List (List Pat)} {srow : List Pat},
    srow ∈ specialize tag n rows →
    ∃ p ps, (p :: ps) ∈ rows
      ∧ ((irrefutable p = true ∧ srow = List.replicate n .wild ++ ps)
        ∨ (∃ qs, p = .ctor tag qs ∧ qs.length = n ∧ srow = qs ++ ps))
  | [], _, h => by simp [specialize] at h
  | [] :: rows, srow, h => by
    simp only [specialize] at h
    obtain ⟨p, ps, hm, hcase⟩ := specialize_mem h
    exact ⟨p, ps, List.mem_cons_of_mem _ hm, hcase⟩
  | (p :: ps') :: rows, srow, h => by
    have lift : srow ∈ specialize tag n rows →
        ∃ q ps, (q :: ps) ∈ (p :: ps') :: rows
          ∧ ((irrefutable q = true ∧ srow = List.replicate n .wild ++ ps)
            ∨ (∃ qs, q = .ctor tag qs ∧ qs.length = n ∧ srow = qs ++ ps)) := by
      intro h'
      obtain ⟨q, qs, hm, hcase⟩ := specialize_mem h'
      exact ⟨q, qs, List.mem_cons_of_mem _ hm, hcase⟩
    cases p with
    | wild =>
      simp only [specialize] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨.wild, ps', List.mem_cons_self .., .inl ⟨rfl, rfl⟩⟩
      · exact lift h
    | bind =>
      simp only [specialize] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨.bind, ps', List.mem_cons_self .., .inl ⟨rfl, rfl⟩⟩
      · exact lift h
    | int k =>
      simp only [specialize] at h
      exact lift h
    | ctor t qs =>
      simp only [specialize] at h
      split at h
      · rename_i hc
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨.ctor t qs, ps', List.mem_cons_self .., .inr ⟨qs, by rw [hc.1], hc.2, rfl⟩⟩
        · exact lift h
      · exact lift h

/-- Patterns matching a list of values in two parts match each part. -/
theorem matchVals_append : ∀ {as : List Pat} {xs : List Value} {bs : List Pat} {ys r : List Value},
    as.length = xs.length → Pat.matchVals (as ++ bs) (xs ++ ys) = some r →
    ∃ r₁ r₂, Pat.matchVals as xs = some r₁ ∧ Pat.matchVals bs ys = some r₂
  | [], [], bs, ys, r, _, h => ⟨[], r, by simp [Pat.matchVals], h⟩
  | a :: as, x :: xs, bs, ys, r, hlen, h => by
    simp only [List.cons_append, Pat.matchVals] at h
    split at h
    · rename_i b rest hb hrest
      obtain ⟨r₁, r₂, h₁, h₂⟩ := matchVals_append (by simpa using hlen) hrest
      exact ⟨b ++ r₁, r₂, by simp [Pat.matchVals, hb, h₁], h₂⟩
    · cases h
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen

theorem matchVals_wilds : ∀ (xs : List Value),
    Pat.matchVals (List.replicate xs.length .wild) xs = some []
  | [] => by simp [Pat.matchVals]
  | x :: xs => by simp [List.replicate, Pat.matchVals, Pat.matchVal, matchVals_wilds xs]

/-- A value of a type that has constructors is built by one of them. -/
theorem ctorsOf_value {S : StoreTy} {v : Value} {T : Ty} {ctors : List (Nat × List Ty)}
    (hc : ctorsOf C T = some ctors) (hv : HasVal C.ctx S v T) :
    ∃ t fields Fs, v = .data t fields ∧ (t, Fs) ∈ ctors ∧ HasVals C.ctx S fields Fs := by
  cases T with
  | tuple Fs =>
    simp only [ctorsOf, Option.some.injEq] at hc
    subst hc
    obtain ⟨t, fields, Fs', rfl, hct, hf⟩ := hv.ctor_inv (tag := 0) (.inl ⟨rfl, rfl⟩)
    rcases hct with ⟨rfl, hT⟩ | ⟨_, _, _, hT, _⟩
    · cases hT
      exact ⟨0, fields, _, rfl, List.mem_cons_self .., hf⟩
    · cases hT
  | data name args =>
    simp only [ctorsOf] at hc
    cases hv with
    | data hct hf =>
      rename_i t fields Fs'
      rcases hct with ⟨_, hT⟩ | ⟨_, name', args', hT, hF⟩
      · cases hT
      · cases hT
        have hF' : (findData C.datas name args).bind (·.lookup t) = some Fs' := hF
        rw [hc] at hF'
        exact ⟨t, fields, Fs', rfl, lookup_mem hF', hf⟩
  | int => simp [ctorsOf] at hc
  | fn _ _ _ => simp [ctorsOf] at hc
  | ref _ => simp [ctorsOf] at hc

/-- What `covers` accepts is covered: every typed list of values is matched by some row. -/
theorem covers_sound : ∀ (fuel : Nat) {rows : List (List Pat)} {tys : List Ty},
    covers C fuel rows tys = true → ∀ {S : StoreTy} {vs : List Value}, HasVals C.ctx S vs tys →
    ∃ row, row ∈ rows ∧ ∃ bs, Pat.matchVals row vs = some bs := by
  intro fuel
  induction fuel with
  | zero => intro rows tys h; simp [covers] at h
  | succ fuel ih =>
    intro rows tys h S vs hvs
    cases tys with
    | nil =>
      cases hvs
      simp only [covers] at h
      obtain ⟨row, hrow, hempty⟩ := List.any_eq_true.mp h
      have e : row = [] := by simpa using hempty
      subst e
      exact ⟨[], hrow, [], by simp [Pat.matchVals]⟩
    | cons T Ts =>
      cases hvs with
      | @cons v vs' _ _ hv hvs' =>
        simp only [covers, Bool.and_eq_true, Bool.or_eq_true] at h
        rcases h.2 with hdef | ⟨_, hctors⟩
        · obtain ⟨ps, hps, bs, hm⟩ := ih hdef hvs'
          obtain ⟨p, hp, hmem⟩ := defaults_mem hps
          obtain ⟨b, hb⟩ := irrefutable_match hp v
          exact ⟨p :: ps, hmem, b ++ bs, by simp [Pat.matchVals, hb, hm]⟩
        · split at hctors
          · rename_i ctors hc
            obtain ⟨t, fields, Fs, rfl, hin, hf⟩ := ctorsOf_value hc hv
            have hcov := List.all_eq_true.mp hctors _ hin
            obtain ⟨srow, hsrow, bs, hm⟩ := ih hcov (hf.append hvs')
            obtain ⟨p, ps, hmem, hcase⟩ := specialize_mem hsrow
            have hlen : fields.length = Fs.length := hf.length_eq
            rcases hcase with ⟨hp, rfl⟩ | ⟨qs, rfl, hqs, rfl⟩
            · obtain ⟨r₁, r₂, _, h₂⟩ := matchVals_append (by simp [hlen]) hm
              obtain ⟨b, hb⟩ := irrefutable_match hp (.data t fields)
              exact ⟨p :: ps, hmem, b ++ r₂, by simp [Pat.matchVals, hb, h₂]⟩
            · obtain ⟨r₁, r₂, h₁, h₂⟩ := matchVals_append (by rw [hqs, hlen]) hm
              exact ⟨.ctor t qs :: ps, hmem, r₁ ++ r₂,
                by simp [Pat.matchVals, Pat.matchVal, h₁, h₂]⟩
          · simp at hctors

/-- If every clause has one pattern per argument and some clause matches, a clause is selected. -/
theorem select_of_match {vs : List Value} : ∀ {cs : List Clause},
    (∀ c, c ∈ cs → c.pats.length = vs.length) →
    (∃ row, row ∈ cs.map (·.pats) ∧ ∃ bs, Pat.matchVals row vs = some bs) →
    selectClause cs vs ≠ none
  | [], _, h => by
    obtain ⟨row, hrow, _⟩ := h
    simp at hrow
  | c :: cs, hlen, h => by
    have hl := hlen c (List.mem_cons_self ..)
    cases hm : Pat.matchVals c.pats vs with
    | some bs => simp [selectClause, hl, hm]
    | none =>
      simp only [selectClause, hl, hm, ↓reduceIte]
      refine select_of_match (fun c' hc' => hlen c' (List.mem_cons_of_mem _ hc')) ?_
      obtain ⟨row, hrow, bs, hbs⟩ := h
      rcases List.mem_cons.mp hrow with rfl | hrow
      · rw [hm] at hbs
        cases hbs
      · exact ⟨row, hrow, bs, hbs⟩

end Glorious.Typing
