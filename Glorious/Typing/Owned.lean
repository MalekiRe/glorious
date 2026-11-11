import Glorious.Typing.Runtime

/-!
# Counting the holders of a resumption

A resumption can be resumed once. The ownership rules are meant to make sure
that nothing can try a second time, and the way to say so is to count: in how
many places of a machine state is a given resumption held where it can still be
used? `occState` is that count. It looks at the locals the rest of the
computation still mentions, at every frame of the stack, at memory, and at the
frames captured in other resumptions. `Unique` says the count is never more
than one, and that a resumption held anywhere has not been used yet.

Nothing here mentions types. Types come in only through `DupSound`: a value of
a type the context calls duplicable holds no resumption.
-/

namespace Glorious.Typing

open Core

mutual

/-- How many times a value holds resumption `id`. -/
def occ (id : Nat) : Value → Nat
  | .int _ => 0
  | .data _ fields => occs id fields
  | .clo _ captures => occs id captures
  | .cont k => if k = id then 1 else 0
  | .label _ => 0
  | .ref _ => 0

def occs (id : Nat) : List Value → Nat
  | [] => 0
  | v :: vs => occ id v + occs id vs

end

theorem occs_append (id : Nat) : ∀ (a b : List Value), occs id (a ++ b) = occs id a + occs id b
  | [], b => by simp [occs]
  | v :: a, b => by simp [occs, occs_append id a b, Nat.add_assoc]

/-! ## Sums over the first `n` numbers -/

def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => total f n + f n

theorem total_le {f g : Nat → Nat} {n : Nat} (h : ∀ i, i < n → f i ≤ g i) :
    total f n ≤ total g n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := h n (Nat.lt_succ_self n)
    simp only [total]
    omega

theorem total_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    total f n = total g n :=
  Nat.le_antisymm (total_le fun i hi => Nat.le_of_eq (h i hi))
    (total_le fun i hi => Nat.le_of_eq (h i hi).symm)

theorem total_add (f g : Nat → Nat) (n : Nat) :
    total (fun i => f i + g i) n = total f n + total g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [total, ih]
    omega

theorem total_ge {f : Nat → Nat} {n i : Nat} (h : i < n) : f i ≤ total f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [total]
    by_cases hi : i < n
    · have := ih hi
      omega
    · have e : i = n := by omega
      subst e
      omega

theorem total_single (a c n : Nat) :
    total (fun i => if i = a then c else 0) n = if a < n then c else 0 := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp only [total, ih]
    rcases Nat.lt_trichotomy a n with h | h | h
    · have h2 : ¬ n = a := by omega
      have h3 : a < n + 1 := by omega
      simp [h, h2, h3]
    · subst h
      simp
    · have h1 : ¬ a < n := by omega
      have h2 : ¬ n = a := by omega
      have h3 : ¬ a < n + 1 := by omega
      simp [h1, h2, h3]

theorem total_succ_front (f : Nat → Nat) (n : Nat) :
    total f (n + 1) = f 0 + total (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    have e : total f (n + 1 + 1) = total f (n + 1) + f (n + 1) := rfl
    rw [e, ih]
    simp only [total]
    omega

theorem total_split (f : Nat → Nat) (a b : Nat) :
    total f (a + b) = total f a + total (fun i => f (a + i)) b := by
  induction b with
  | zero => simp [total]
  | succ b ih =>
    have e : a + (b + 1) = a + b + 1 := by omega
    rw [e]
    simp only [total, ih]
    omega

/-! ## Locals -/

/-- How many times local `i` holds resumption `id`; nothing, if there is no such local. -/
def occAt (id : Nat) (env : Env) (i : Nat) : Nat :=
  match env[i]? with
  | some v => occ id v
  | none => 0

/-- How many times the locals in `live` hold resumption `id`. -/
def occEnv (id : Nat) (env : Env) (live : List Nat) : Nat :=
  total (fun i => if i ∈ live then occAt id env i else 0) env.length

/-- The same, for a list of locals that may repeat. -/
def sumAt (id : Nat) (env : Env) : List Nat → Nat
  | [] => 0
  | i :: is => occAt id env i + sumAt id env is

theorem occAt_eq {id : Nat} {env : Env} {i : Nat} {v : Value} (h : env[i]? = some v) :
    occAt id env i = occ id v := by
  simp [occAt, h]

theorem occAt_none {id : Nat} {env : Env} {i : Nat} (h : env.length ≤ i) :
    occAt id env i = 0 := by
  simp [occAt, List.getElem?_eq_none h]

theorem total_occAt (id : Nat) : ∀ (l : List Value),
    total (fun i => occAt id l i) l.length = occs id l
  | [] => rfl
  | v :: l => by
    rw [List.length_cons, total_succ_front]
    have h : total (fun i => occAt id (v :: l) (i + 1)) l.length
        = total (fun i => occAt id l i) l.length :=
      total_congr fun i _ => by simp [occAt]
    rw [h, total_occAt id l]
    simp [occAt, occs]

theorem occEnv_mono {id : Nat} {env : Env} {a b : List Nat} (h : ∀ i, i ∈ a → i ∈ b) :
    occEnv id env a ≤ occEnv id env b := by
  refine total_le fun i _ => ?_
  by_cases hi : i ∈ a
  · simp [hi, h i hi]
  · simp only [hi, ↓reduceIte]
    exact Nat.zero_le _

theorem occEnv_ge {id : Nat} {env : Env} {live : List Nat} {i : Nat} {v : Value}
    (hi : i ∈ live) (hv : env[i]? = some v) : occ id v ≤ occEnv id env live := by
  have hlt : i < env.length := by
    rcases Nat.lt_or_ge i env.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hv
      cases hv
  have := total_ge (f := fun i => if i ∈ live then occAt id env i else 0) hlt
  unfold occEnv
  simpa [hi, occAt_eq hv] using this

/-- A new local adds at most what its value holds. -/
theorem occEnv_push (id : Nat) (env : Env) (w : Value) (live : List Nat) :
    occEnv id (env ++ [w]) live ≤ occEnv id env live + occ id w := by
  have e : (env ++ [w]).length = env.length + 1 := by simp
  unfold occEnv
  rw [e]
  simp only [total]
  have h1 : total (fun i => if i ∈ live then occAt id (env ++ [w]) i else 0) env.length
      = total (fun i => if i ∈ live then occAt id env i else 0) env.length :=
    total_congr fun i hi => by simp [occAt, List.getElem?_append_left hi]
  have h2 : occAt id (env ++ [w]) env.length = occ id w := by simp [occAt]
  rw [h1, h2]
  split <;> omega

theorem occEnv_nil (id : Nat) (env : Env) : occEnv id env [] = 0 := by
  have h : total (fun i => if i ∈ ([] : List Nat) then occAt id env i else 0) env.length
      = total (fun _ => 0) env.length := total_congr fun i _ => by simp
  have z : ∀ n, total (fun _ => 0) n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [total, ih]
  unfold occEnv
  rw [h, z]

theorem cnt_pos {i : Nat} : ∀ {l : List Nat}, i ∈ l → 0 < cnt i l
  | a :: l, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [cnt, ↓reduceIte]
      omega
    · have := cnt_pos h
      simp only [cnt]
      omega

theorem cnt_zero {i : Nat} : ∀ {l : List Nat}, i ∉ l → cnt i l = 0
  | [], _ => rfl
  | a :: l, h => by
    have h1 : ¬ a = i := fun e => h (e ▸ List.mem_cons_self ..)
    have h2 := cnt_zero (l := l) (fun hm => h (List.mem_cons_of_mem _ hm))
    simp [cnt, h1, h2]

theorem sumAt_total (id : Nat) (env : Env) : ∀ (vars : List Nat),
    sumAt id env vars = total (fun i => cnt i vars * occAt id env i) env.length
  | [] => by
    have h : total (fun i => cnt i [] * occAt id env i) env.length
        = total (fun i => if i ∈ ([] : List Nat) then occAt id env i else 0) env.length :=
      total_congr fun i _ => by simp [cnt]
    rw [h]
    exact (occEnv_nil id env).symm
  | a :: vars => by
    have h : total (fun i => cnt i (a :: vars) * occAt id env i) env.length
        = total (fun i => (if i = a then occAt id env a else 0) + cnt i vars * occAt id env i)
            env.length :=
      total_congr fun i _ => by
        by_cases e : a = i
        · subst e
          simp [cnt, Nat.add_mul]
        · have e' : ¬ i = a := fun h => e h.symm
          simp [cnt, e, e']
    rw [h, total_add, total_single, ← sumAt_total id env vars]
    simp only [sumAt]
    by_cases hlt : a < env.length
    · simp [hlt]
    · simp [hlt, occAt_none (id := id) (Nat.le_of_not_lt hlt)]

theorem sumAt_append (id : Nat) (env : Env) : ∀ (a b : List Nat),
    sumAt id env (a ++ b) = sumAt id env a + sumAt id env b
  | [], b => by simp [sumAt]
  | i :: a, b => by simp [sumAt, sumAt_append id env a b, Nat.add_assoc]

/-- What evaluated operands hold is what the locals they name hold. -/
theorem occs_evalAtoms (id : Nat) (env : Env) : ∀ (as : List Atom) {vs : List Value},
    evalAtoms env as = some vs → occs id vs = sumAt id env (atomVars as)
  | [], vs, h => by
    simp only [evalAtoms, Option.some.injEq] at h
    subst h
    rfl
  | a :: as, vs, h => by
    simp only [evalAtoms] at h
    split at h
    · rename_i v vs' hv hvs
      cases h
      have ih := occs_evalAtoms id env as hvs
      cases a with
      | var i =>
        have hv' : env[i]? = some v := hv
        simp [occs, atomVars, sumAt, occAt_eq hv', ih]
      | int n =>
        simp only [Atom.eval, Option.some.injEq] at hv
        subst hv
        simp [occs, occ, atomVars, ih]
    · cases h

theorem occ_eval (id : Nat) (env : Env) {a : Atom} {v : Value} (h : a.eval env = some v) :
    occ id v = sumAt id env (atomVars [a]) := by
  have := occs_evalAtoms id env [a] (vs := [v]) (by simp [evalAtoms, h])
  simpa [occs] using this

/-! ## Types enter here -/

/-- A value of a type the context calls duplicable holds no resumption. -/
def DupSound (Δ : Ctx) : Prop :=
  ∀ S v τ, HasVal Δ S v τ → Δ.dup τ → ∀ id, occ id v = 0

theorem HasVals.get' {Δ : Ctx} {S : StoreTy} :
    ∀ {vs : List Value} {τs : List Ty} {i : Nat} {v : Value}, HasVals Δ S vs τs →
      vs[i]? = some v → ∃ τ, τs[i]? = some τ ∧ HasVal Δ S v τ
  | _, _, _, _, .nil, h => by simp at h
  | _, _, 0, _, .cons hv _, h => by
    simp at h
    subst h
    exact ⟨_, by simp, hv⟩
  | _, _, i + 1, _, .cons _ hs, h => by
    simp at h
    simpa using HasVals.get' hs h

theorem occs_dup {Δ : Ctx} {S : StoreTy} (hD : DupSound Δ) (id : Nat) :
    ∀ {vs : List Value} {τs : List Ty}, HasVals Δ S vs τs → (∀ c, c ∈ τs → Δ.dup c) →
      occs id vs = 0
  | _, _, .nil, _ => rfl
  | _, _, .cons hv hvs, h => by
    simp [occs, hD _ _ _ hv (h _ (List.mem_cons_self ..)) id,
      occs_dup hD id hvs (fun c hc => h c (List.mem_cons_of_mem _ hc))]

/--
Moving locals out of an activation. If the moved locals are used linearly with
respect to what is mentioned afterwards, then what the rest still holds and
what was moved out together are no more than what the activation held.
-/
theorem moved_le {Δ : Ctx} {S : StoreTy} {env : Env} {Γ : TEnv} {moved rest : List Nat}
    (hD : DupSound Δ) (henv : HasVals Δ S env Γ) (hlin : Linear Δ Γ moved rest) (id : Nat) :
    occEnv id env rest + sumAt id env moved ≤ occEnv id env (moved ++ rest) := by
  rw [sumAt_total]
  unfold occEnv
  rw [← total_add]
  refine total_le fun i hi => ?_
  obtain ⟨v, hv⟩ : ∃ v, env[i]? = some v := ⟨env[i], List.getElem?_eq_getElem hi⟩
  rw [occAt_eq hv]
  by_cases hz : occ id v = 0
  · simp [hz]
  · obtain ⟨τ, hτ, hvt⟩ := henv.get' hv
    have hnd : ¬ Δ.dup τ := fun hd => hz (hD _ _ _ hvt hd id)
    obtain ⟨hc, hex⟩ := hlin i τ hτ hnd
    by_cases hm : i ∈ moved
    · have hpos := cnt_pos hm
      have h1 : cnt i moved = 1 := by omega
      have hr : i ∉ rest := hex hm
      simp [h1, hr, hm]
    · simp [cnt_zero hm, hm]

/-! ## Patterns and entering a function -/

mutual

/-- What a pattern binds holds no more than the value it was matched against. -/
theorem matchVal_occ (id : Nat) : ∀ (p : Pat) (v : Value) {bs : List Value},
    p.matchVal v = some bs → occs id bs ≤ occ id v
  | .wild, v, bs, h => by
    simp only [Pat.matchVal, Option.some.injEq] at h
    subst h
    simp [occs]
  | .bind, v, bs, h => by
    simp only [Pat.matchVal, Option.some.injEq] at h
    subst h
    simp [occs]
  | .int n, v, bs, h => by
    cases v with
    | int m =>
      simp [Pat.matchVal] at h
      obtain ⟨_, rfl⟩ := h
      simp [occs]
    | _ => simp [Pat.matchVal] at h
  | .ctor tag ps, v, bs, h => by
    cases v with
    | data t fields =>
      simp [Pat.matchVal] at h
      simpa [occ] using matchVals_occ id ps fields h.2
    | _ => simp [Pat.matchVal] at h

theorem matchVals_occ (id : Nat) : ∀ (ps : List Pat) (vs : List Value) {bs : List Value},
    Pat.matchVals ps vs = some bs → occs id bs ≤ occs id vs
  | [], [], bs, h => by
    simp only [Pat.matchVals, Option.some.injEq] at h
    subst h
    simp [occs]
  | p :: ps, v :: vs, bs, h => by
    simp only [Pat.matchVals] at h
    split at h
    · rename_i b bs' hb hbs
      cases h
      have h1 := matchVal_occ id p v hb
      have h2 := matchVals_occ id ps vs hbs
      simp only [occs_append, occs]
      omega
    · cases h
  | [], _ :: _, _, h => by simp [Pat.matchVals] at h
  | _ :: _, [], _, h => by simp [Pat.matchVals] at h

end

theorem matchVal_wild {p : Pat} {v : Value} {bs : List Value} (hw : isWild p = true)
    (h : p.matchVal v = some bs) : bs = [] := by
  cases p with
  | wild =>
    simp only [Pat.matchVal, Option.some.injEq] at h
    exact h.symm
  | bind => simp [isWild] at hw
  | int n => simp [isWild] at hw
  | ctor t ps => simp [isWild] at hw

/-- What the arguments at wildcard positions hold. -/
def wildOcc (id : Nat) (ps : List Pat) (vs : List Value) (i : Nat) : Nat :=
  match ps[i]?, vs[i]? with
  | some p, some v => if isWild p then occ id v else 0
  | _, _ => 0

/-- The bindings and the arguments left whole together hold no more than the arguments. -/
theorem matchVals_wild_occ (id : Nat) : ∀ (ps : List Pat) (vs : List Value) {bs : List Value},
    Pat.matchVals ps vs = some bs →
    occs id bs + total (wildOcc id ps vs) vs.length ≤ occs id vs
  | [], [], bs, h => by
    simp only [Pat.matchVals, Option.some.injEq] at h
    subst h
    simp [occs, total]
  | p :: ps, v :: vs, bs, h => by
    simp only [Pat.matchVals] at h
    split at h
    · rename_i b bs' hb hbs
      cases h
      have ih := matchVals_wild_occ id ps vs hbs
      have hshift : total (fun i => wildOcc id (p :: ps) (v :: vs) (i + 1)) vs.length
          = total (wildOcc id ps vs) vs.length :=
        total_congr fun i _ => by simp [wildOcc]
      rw [List.length_cons, total_succ_front, hshift]
      have h0 : wildOcc id (p :: ps) (v :: vs) 0 = if isWild p then occ id v else 0 := by
        simp [wildOcc]
      rw [h0]
      cases hq : isWild p with
      | true =>
        have e := matchVal_wild hq hb
        subst e
        simp only [occs_append, occs, ↓reduceIte]
        omega
      | false =>
        have h1 := matchVal_occ id p v hb
        simp only [occs_append, occs, Bool.false_eq_true, ↓reduceIte]
        omega
    · cases h
  | [], _ :: _, _, h => by simp [Pat.matchVals] at h
  | _ :: _, [], _, h => by simp [Pat.matchVals] at h

/--
The environment a clause starts in holds no more than the arguments and the
captures did, as long as the clause's body does not mention an argument its
pattern took apart.
-/
theorem clause_env_le (id : Nat) {pats : List Pat} {vs captures bs : List Value}
    {live : List Nat} (hm : Pat.matchVals pats vs = some bs) (hlen : pats.length = vs.length)
    (hw : ∀ i p, pats[i]? = some p → isWild p = false → i ∉ live) :
    occEnv id (vs ++ captures ++ bs) live ≤ occs id vs + occs id captures := by
  have hmv := matchVals_wild_occ id pats vs hm
  have e : (vs ++ captures ++ bs).length = vs.length + (captures ++ bs).length := by
    simp only [List.length_append]
    omega
  unfold occEnv
  rw [e, total_split]
  have hA : total (fun i => if i ∈ live then occAt id (vs ++ captures ++ bs) i else 0) vs.length
      ≤ total (wildOcc id pats vs) vs.length := by
    refine total_le fun i hi => ?_
    obtain ⟨p, hp⟩ : ∃ p, pats[i]? = some p :=
      ⟨pats[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hv : vs[i]? = some vs[i] := List.getElem?_eq_getElem hi
    have hv' : (vs ++ captures ++ bs)[i]? = some vs[i] := by
      rw [List.append_assoc, List.getElem?_append_left hi]
      exact hv
    by_cases hl : i ∈ live
    · have hwild : isWild p = true := by
        cases hq : isWild p with
        | true => rfl
        | false => exact absurd hl (hw i p hp hq)
      simp only [hl, ↓reduceIte]
      rw [occAt_eq hv']
      simp [wildOcc, hp, hv, hwild]
    · simp [hl]
  have hB : total (fun i => if vs.length + i ∈ live
        then occAt id (vs ++ captures ++ bs) (vs.length + i) else 0) (captures ++ bs).length
      ≤ occs id (captures ++ bs) := by
    rw [← total_occAt id (captures ++ bs)]
    refine total_le fun i _ => ?_
    have hshift : occAt id (vs ++ captures ++ bs) (vs.length + i) = occAt id (captures ++ bs) i := by
      simp [occAt, List.append_assoc, List.getElem?_append_right]
    rw [hshift]
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  have hbs := occs_append id captures bs
  omega

/-! ## Frames, memory and captured frames -/

def occAfter (id : Nat) : After → Nat
  | .yield v => occ id v
  | .invoke _ captures args => occs id captures + occs id args

/-- How many times a frame holds resumption `id`. A suspended caller holds what
the locals its code still mentions hold. -/
def occFrame (id : Nat) : Frame → Nat
  | .call env body => occEnv id env (fv body)
  | .handler _ h => occs id h.caps
  | .label _ => 0
  | .guard _ captures => occs id captures
  | .yield w => occ id w
  | .exit _ after => occAfter id after

def occStack (id : Nat) : List Frame → Nat
  | [] => 0
  | fr :: st => occFrame id fr + occStack id st

theorem occStack_append (id : Nat) : ∀ (a b : List Frame),
    occStack id (a ++ b) = occStack id a + occStack id b
  | [], b => by simp [occStack]
  | fr :: a, b => by simp [occStack, occStack_append id a b, Nat.add_assoc]

/-- A sum over the filled entries of a list of optional things. -/
def osum {α : Type} (w : α → Nat) : List (Option α) → Nat
  | [] => 0
  | some x :: l => w x + osum w l
  | none :: l => osum w l

def oweight {α : Type} (w : α → Nat) : Option α → Nat
  | some x => w x
  | none => 0

theorem osum_append {α : Type} (w : α → Nat) : ∀ (a b : List (Option α)),
    osum w (a ++ b) = osum w a + osum w b
  | [], b => by simp [osum]
  | some x :: a, b => by simp [osum, osum_append w a b, Nat.add_assoc]
  | none :: a, b => by simp [osum, osum_append w a b]

theorem osum_set {α : Type} (w : α → Nat) : ∀ (l : List (Option α)) (i : Nat) (x old : Option α),
    l[i]? = some old → osum w (l.set i x) + oweight w old = osum w l + oweight w x
  | [], _, _, _, h => by simp at h
  | c :: l, 0, x, old, h => by
    simp at h
    subst h
    cases c <;> cases x <;> simp [osum, oweight] <;> omega
  | c :: l, i + 1, x, old, h => by
    simp at h
    have ih := osum_set w l i x old h
    cases c <;> simp [osum] <;> omega

def occCells (id : Nat) (cells : Cells) : Nat := osum (occ id) cells

def occConts (id : Nat) (conts : Conts Frame) : Nat := osum (occStack id) conts

/-- How many times a machine state holds resumption `id` where it can still be used. -/
def occState (id : Nat) (s : State) : Nat :=
  occEnv id s.env (fv s.tm) + occStack id s.stack + occCells id s.store.cells
    + occConts id s.store.conts

/-- No resumption is held in two places, and one that is held has not been used. -/
def Unique (s : State) : Prop :=
  ∀ id, occState id s ≤ 1 ∧ (0 < occState id s → ∃ seg, s.store.conts[id]? = some (some seg))

/-- The state changed without touching the resumptions, and holds no more than before. -/
theorem Unique.mono {s s' : State} (hu : Unique s) (hc : s'.store.conts = s.store.conts)
    (h : ∀ id, occState id s' ≤ occState id s) : Unique s' := by
  intro id
  obtain ⟨h1, h2⟩ := hu id
  have := h id
  refine ⟨by omega, fun hp => ?_⟩
  rw [hc]
  exact h2 (by omega)

/-- Resumption `k` was used, and the one place that held it holds it no longer. -/
theorem Unique.take {s s' : State} {k : Nat} (hu : Unique s)
    (hc : s'.store.conts = s.store.conts.set k none)
    (h : ∀ id, occState id s' + (if k = id then 1 else 0) ≤ occState id s) : Unique s' := by
  intro id
  obtain ⟨h1, h2⟩ := hu id
  have := h id
  by_cases e : k = id
  · subst e
    simp only [↓reduceIte] at this
    exact ⟨by omega, fun hp => by omega⟩
  · simp only [e, ↓reduceIte] at this
    refine ⟨by omega, fun hp => ?_⟩
    obtain ⟨seg, hseg⟩ := h2 (by omega)
    refine ⟨seg, ?_⟩
    rw [hc, List.getElem?_set]
    simp [e, hseg]

/-- A new resumption was made, and is held in at most one place. -/
theorem Unique.fresh {s s' : State} {seg : List Frame} (hu : Unique s)
    (hc : s'.store.conts = s.store.conts ++ [some seg])
    (h : ∀ id, occState id s' ≤ occState id s + (if s.store.conts.length = id then 1 else 0)) :
    Unique s' := by
  intro id
  obtain ⟨h1, h2⟩ := hu id
  have := h id
  by_cases e : s.store.conts.length = id
  · subst e
    have hz : occState s.store.conts.length s = 0 := by
      rcases Nat.eq_zero_or_pos (occState s.store.conts.length s) with hz | hp
      · exact hz
      · obtain ⟨seg', hseg⟩ := h2 hp
        simp at hseg
    simp only [↓reduceIte, hz] at this
    exact ⟨by omega, fun _ => ⟨seg, by rw [hc]; simp⟩⟩
  · simp only [e, ↓reduceIte] at this
    refine ⟨by omega, fun hp => ?_⟩
    obtain ⟨seg', hseg⟩ := h2 (by omega)
    refine ⟨seg', ?_⟩
    have hlt : id < s.store.conts.length := by
      rcases Nat.lt_or_ge id s.store.conts.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hseg
        cases hseg
    rw [hc, List.getElem?_append_left hlt]
    exact hseg

/-! ## Small facts used step by step -/

theorem occ_unit (id : Nat) : occ id Value.unit = 0 := by simp [Value.unit, occ, occs]

theorem Linear.nil {Δ : Ctx} {Γ : TEnv} {rest : List Nat} : Linear Δ Γ [] rest :=
  fun _ _ _ _ => ⟨Nat.zero_le _, fun h => by cases h⟩

/-- One local moved once, with nothing after it. -/
theorem Linear.single {Δ : Ctx} {Γ : TEnv} (a : Atom) : Linear Δ Γ (atomVars [a]) [] := by
  intro i τ _ _
  cases a with
  | var j =>
    refine ⟨?_, fun _ h => by cases h⟩
    by_cases e : j = i <;> simp [atomVars, cnt, e]
  | int n => exact ⟨Nat.zero_le _, fun _ h => by cases h⟩

/-- What is still mentioned and what is moved out are, together, no more than
what the locals mentioned before the step hold. -/
theorem moved_live {Δ : Ctx} {S : StoreTy} {env : Env} {Γ : TEnv} {moved rest live : List Nat}
    (hD : DupSound Δ) (henv : HasVals Δ S env Γ) (hlin : Linear Δ Γ moved rest)
    (hsub : ∀ i, i ∈ moved ++ rest → i ∈ live) (id : Nat) :
    occEnv id env rest + sumAt id env moved ≤ occEnv id env live :=
  Nat.le_trans (moved_le hD henv hlin id) (occEnv_mono hsub)

theorem occ_atom_le (id : Nat) {env : Env} {a : Atom} {v : Value} {live : List Nat}
    (h : a.eval env = some v) (hsub : ∀ i, i ∈ atomVars [a] → i ∈ live) :
    occ id v ≤ occEnv id env live := by
  cases a with
  | var i => exact occEnv_ge (hsub i (by simp [atomVars])) h
  | int n =>
    simp only [Atom.eval, Option.some.injEq] at h
    subst h
    simp [occ]

theorem rhsMoves_sub {rhs : Rhs} {i : Nat} (h : i ∈ rhsMoves rhs) : i ∈ rhsVars rhs := by
  cases rhs with
  | atom a => exact h
  | prim p args => cases h
  | construct tag args => exact h
  | place pl => cases h
  | closure fn captures => exact h

theorem atomVars_tail_sub {a : Atom} {as : List Atom} {i : Nat} (h : i ∈ atomVars as) :
    i ∈ atomVars (a :: as) := by
  cases a with
  | var j => exact List.mem_cons_of_mem _ h
  | int n => exact h

theorem atomVars_head_sub {a : Atom} {as : List Atom} {i : Nat} (h : i ∈ atomVars [a]) :
    i ∈ atomVars (a :: as) := by
  cases a with
  | var j =>
    simp only [atomVars, List.mem_singleton] at h
    subst h
    exact List.mem_cons_self ..
  | int n => cases h

theorem occCells_push (id : Nat) (cells : Cells) (v : Value) :
    occCells id (cells ++ [some v]) = occCells id cells + occ id v := by
  simp [occCells, osum_append, osum]

theorem occCells_set (id : Nat) {cells : Cells} {a : Nat} {old : Option Value}
    (h : cells[a]? = some old) (x : Option Value) :
    occCells id (cells.set a x) + oweight (occ id) old = occCells id cells + oweight (occ id) x :=
  osum_set (occ id) cells a x old h

theorem occConts_push (id : Nat) (conts : Conts Frame) (seg : List Frame) :
    occConts id (conts ++ [some seg]) = occConts id conts + occStack id seg := by
  simp [occConts, osum_append, osum]

theorem occConts_take (id : Nat) {conts : Conts Frame} {k : Nat} {seg : List Frame}
    (h : conts[k]? = some (some seg)) :
    occConts id (conts.set k none) + occStack id seg = occConts id conts := by
  have := osum_set (occStack id) conts k none (some seg) h
  simpa [occConts, oweight] using this

theorem calleeAtom_fv {tm : Tm} {i : Nat} (h : calleeAtom tm = some (.var i)) : i ∈ fv tm := by
  cases tm <;> simp [calleeAtom] at h <;> subst h <;> simp [fv, atomVars]

/-- A resumption that some part of the computation is about to use is held, so it is unused. -/
def Resumed (s : State) : Prop :=
  ∃ f id, calleeAtom s.tm = some f ∧ f.eval s.env = some (.cont id)
    ∧ s.store.conts[id]? = some none

theorem Unique.not_resumed {s : State} (hu : Unique s) : ¬ Resumed s := by
  rintro ⟨f, id, hf, hev, hnone⟩
  cases f with
  | int n => simp [Atom.eval] at hev
  | var i =>
    have hge := occEnv_ge (id := id) (calleeAtom_fv hf) (show s.env[i]? = some (.cont id) from hev)
    obtain ⟨_, hlive⟩ := hu id
    have hpos : 0 < occState id s := by
      simp only [occ, ↓reduceIte] at hge
      simp only [occState]
      omega
    obtain ⟨seg, hseg⟩ := hlive hpos
    rw [hseg] at hnone
    cases hnone

/-- The frames a handler search splits the stack into are the stack. -/
theorem findHandler_split {op : Nat} : ∀ {st : List Frame} {d : Dispatch Frame},
    findHandler Frame.asHandler op st = some d →
    st = d.above ++ .handler d.id d.handler :: d.below
  | [], _, h => by simp [findHandler] at h
  | fr :: st, d, h => by
    cases hx : handles Frame.asHandler op fr with
    | some r =>
      obtain ⟨id, hd, arm⟩ := r
      simp [findHandler, hx] at h
      subst h
      cases fr with
      | handler id' h' =>
        simp only [handles, Frame.asHandler] at hx
        split at hx
        · cases hx
          rfl
        · cases hx
      | _ => simp [handles, Frame.asHandler] at hx
    | none =>
      cases hf : findHandler Frame.asHandler op st with
      | none => simp [findHandler, hx, hf] at h
      | some d₀ =>
        simp [findHandler, hx, hf] at h
        subst h
        have := findHandler_split hf
        simp [← this]

end Glorious.Typing
