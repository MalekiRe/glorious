import Glorious.Compile
import Glorious.Core.Semantics
import Glorious.Bytecode.Semantics
import Glorious.Proof.CodeAt

/-!
# Pattern compilation

The compiler turns each clause into a list of tests and a list of bound places.
This file shows that those lists mean the same as the Core matching semantics,
and that the machine executes them accordingly: a matching clause reaches its
body with the bindings loaded, a failing clause reaches the next clause with
the locals untouched.
-/

namespace Glorious

open Machine
open Bytecode (Instr Code)
open Core (Pat)

/-! ## Places -/

theorem Value.follow_snoc {v : Value} {path : List Nat} {tag : Nat} {fields : List Value}
    {i : Nat} {field : Value} (h : v.follow path = some (.data tag fields))
    (hf : fields[i]? = some field) : v.follow (path ++ [i]) = some field := by
  induction path generalizing v with
  | nil =>
    simp [Value.follow] at h
    subst h
    simp [Value.follow, hf]
  | cons j path ih =>
    cases v with
    | int n => simp [Value.follow] at h
    | clo fn caps => simp [Value.follow] at h
    | cont id => simp [Value.follow] at h
    | label id => simp [Value.follow] at h
    | data t fs =>
      simp only [List.cons_append, Value.follow] at h ⊢
      cases hg : fs[j]? with
      | none => simp [hg] at h
      | some g =>
        simp only [hg] at h ⊢
        exact ih h

theorem Place.eval_child {ρ : Env} {pl : Place} {tag : Nat} {fields : List Value} {i : Nat}
    {field : Value} (h : pl.eval ρ = some (.data tag fields)) (hf : fields[i]? = some field) :
    (pl.child i).eval ρ = some field := by
  unfold Place.eval at h ⊢
  simp only [Place.child]
  cases hv : ρ[pl.var]? with
  | none => simp [hv] at h
  | some v =>
    simp only [hv] at h ⊢
    exact Value.follow_snoc h hf

/-- Loading more locals does not change what an existing place holds. -/
theorem Place.eval_append {ρ ρ' : Env} {pl : Place} {v : Value} (h : pl.eval ρ = some v) :
    pl.eval (ρ ++ ρ') = some v := by
  unfold Place.eval at h ⊢
  cases hv : ρ[pl.var]? with
  | none => simp [hv] at h
  | some w =>
    rw [getElem?_append_of_eq_some hv]
    simpa [hv] using h

theorem argPlace_eval {ρ : Env} {j : Nat} {v : Value} (h : ρ[j]? = some v) :
    (argPlace j).eval ρ = some v := by
  simp [Place.eval, argPlace, h, Value.follow]

/-! ## What the generated tests and bindings mean -/

/-- Whether a test holds; `none` if its place does not exist. -/
def Test.check (ρ : Env) : Test → Option Bool
  | .ctor pl tag arity => (pl.eval ρ).map (·.isCtor tag arity)
  | .int pl n => (pl.eval ρ).map (·.isInt n)

/-- Run tests in order, stopping at the first that does not hold. -/
def checkAll (ρ : Env) : List Test → Option Bool
  | [] => some true
  | t :: ts =>
    match t.check ρ with
    | some true => checkAll ρ ts
    | some false => some false
    | none => none

theorem checkAll_append (ρ : Env) (a b : List Test) :
    checkAll ρ (a ++ b) =
      match checkAll ρ a with
      | some true => checkAll ρ b
      | some false => some false
      | none => none := by
  induction a with
  | nil => simp [checkAll]
  | cons t a ih =>
    simp only [List.cons_append, checkAll]
    cases t.check ρ with
    | none => rfl
    | some r =>
      cases r with
      | true => exact ih
      | false => rfl

def evalPlaces (ρ : Env) : List Place → Option (List Value)
  | [] => some []
  | pl :: pls =>
    match pl.eval ρ, evalPlaces ρ pls with
    | some v, some vs => some (v :: vs)
    | _, _ => none

theorem evalPlaces_append {ρ : Env} {a b : List Place} {x y : List Value}
    (ha : evalPlaces ρ a = some x) (hb : evalPlaces ρ b = some y) :
    evalPlaces ρ (a ++ b) = some (x ++ y) := by
  induction a generalizing x with
  | nil =>
    simp [evalPlaces] at ha
    subst ha
    simpa using hb
  | cons pl a ih =>
    simp only [evalPlaces] at ha
    cases hp : pl.eval ρ with
    | none => simp [hp] at ha
    | some v =>
      cases hr : evalPlaces ρ a with
      | none => simp [hp, hr] at ha
      | some vs =>
        simp [hp, hr] at ha
        subst ha
        simp [evalPlaces, hp, ih hr]

theorem matchVals_length {ps : List Pat} : ∀ {vs bs : List Value},
    Pat.matchVals ps vs = some bs → ps.length = vs.length := by
  induction ps with
  | nil =>
    intro vs bs h
    cases vs with
    | nil => rfl
    | cons v vs => simp [Pat.matchVals] at h
  | cons p ps ih =>
    intro vs bs h
    cases vs with
    | nil => simp [Pat.matchVals] at h
    | cons v vs =>
      cases hp : p.matchVal v with
      | none => simp [Pat.matchVals, hp] at h
      | some b =>
        cases hps : Pat.matchVals ps vs with
        | none => simp [Pat.matchVals, hp, hps] at h
        | some bs' => simp [ih hps]

theorem matchVals_eq_none {ps : List Pat} {vs : List Value} (h : ps.length ≠ vs.length) :
    Pat.matchVals ps vs = none := by
  cases hm : Pat.matchVals ps vs with
  | none => rfl
  | some bs => exact absurd (matchVals_length hm) h

mutual

/-- The tests of a pattern all hold exactly when the pattern matches. -/
theorem patTests_check (ρ : Env) : ∀ (p : Pat) (pl : Place) (v : Value), pl.eval ρ = some v →
    checkAll ρ (patTests p pl) = some (p.matchVal v).isSome
  | .wild, _, _, _ => by simp [patTests, checkAll, Pat.matchVal]
  | .bind, _, _, _ => by simp [patTests, checkAll, Pat.matchVal]
  | .int n, pl, v, hv => by
    cases v with
    | int m =>
      by_cases h : n = m
      · simp [patTests, checkAll, Test.check, hv, Value.isInt, Pat.matchVal, h]
      · have hb : (n == m) = false := by simpa using h
        simp [patTests, checkAll, Test.check, hv, Value.isInt, Pat.matchVal, h, hb]
    | data t fs => simp [patTests, checkAll, Test.check, hv, Value.isInt, Pat.matchVal]
    | clo f cs => simp [patTests, checkAll, Test.check, hv, Value.isInt, Pat.matchVal]
    | cont id => simp [patTests, checkAll, Test.check, hv, Value.isInt, Pat.matchVal]
    | label id => simp [patTests, checkAll, Test.check, hv, Value.isInt, Pat.matchVal]
  | .ctor tag ps, pl, v, hv => by
    cases v with
    | int m => simp [patTests, checkAll, Test.check, hv, Value.isCtor, Pat.matchVal]
    | clo f cs => simp [patTests, checkAll, Test.check, hv, Value.isCtor, Pat.matchVal]
    | cont id => simp [patTests, checkAll, Test.check, hv, Value.isCtor, Pat.matchVal]
    | label id => simp [patTests, checkAll, Test.check, hv, Value.isCtor, Pat.matchVal]
    | data t fs =>
      by_cases ht : tag = t
      · by_cases hl : ps.length = fs.length
        · have ih := patsTests_check ρ ps pl.child fs hl
            (fun j w hj => Place.eval_child hv hj)
          simp [patTests, checkAll, Test.check, hv, Value.isCtor, Pat.matchVal, ht, hl, ih]
        · have hn : Pat.matchVals ps fs = none := matchVals_eq_none hl
          have hb : (ps.length == fs.length) = false := by simpa using hl
          simp [patTests, checkAll, Test.check, hv, Value.isCtor, Pat.matchVal, ht, hn, hb]
      · have hb : (tag == t) = false := by simpa using ht
        simp [patTests, checkAll, Test.check, hv, Value.isCtor, Pat.matchVal, ht, hb]

theorem patsTests_check (ρ : Env) : ∀ (ps : List Pat) (mk : Nat → Place) (vs : List Value),
    ps.length = vs.length → (∀ j v, vs[j]? = some v → (mk j).eval ρ = some v) →
    checkAll ρ (patsTests ps mk) = some (Pat.matchVals ps vs).isSome
  | [], _, vs, hl, _ => by
    cases vs with
    | nil => simp [patsTests, checkAll, Pat.matchVals]
    | cons v vs => simp at hl
  | p :: ps, mk, vs, hl, hmk => by
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      have ih₁ := patTests_check ρ p (mk 0) v (hmk 0 v (by simp))
      have ih₂ := patsTests_check ρ ps (fun j => mk (j + 1)) vs (by simpa using hl)
        (fun j w hj => hmk (j + 1) w (by simpa using hj))
      rw [patsTests, checkAll_append, ih₁, ih₂]
      cases hp : p.matchVal v <;> cases hps : Pat.matchVals ps vs <;>
        simp [Pat.matchVals, hp, hps]

end

mutual

/-- The places a matching pattern binds hold exactly the values it binds. -/
theorem patBinds_eval (ρ : Env) : ∀ (p : Pat) (pl : Place) (v : Value) (bs : List Value),
    pl.eval ρ = some v → p.matchVal v = some bs → evalPlaces ρ (patBinds p pl) = some bs
  | .wild, _, _, _, _, hm => by
    simp [Pat.matchVal] at hm
    subst hm
    simp [patBinds, evalPlaces]
  | .bind, _, _, _, hv, hm => by
    simp [Pat.matchVal] at hm
    subst hm
    simp [patBinds, evalPlaces, hv]
  | .int n, _, v, _, _, hm => by
    cases v with
    | int m =>
      by_cases h : n = m
      · simp [Pat.matchVal, h] at hm
        subst hm
        simp [patBinds, evalPlaces]
      · simp [Pat.matchVal, h] at hm
    | data t fs => simp [Pat.matchVal] at hm
    | clo f cs => simp [Pat.matchVal] at hm
    | cont id => simp [Pat.matchVal] at hm
    | label id => simp [Pat.matchVal] at hm
  | .ctor tag ps, pl, v, bs, hv, hm => by
    cases v with
    | int m => simp [Pat.matchVal] at hm
    | clo f cs => simp [Pat.matchVal] at hm
    | cont id => simp [Pat.matchVal] at hm
    | label id => simp [Pat.matchVal] at hm
    | data t fs =>
      by_cases ht : tag = t
      · simp [Pat.matchVal, ht] at hm
        simpa [patBinds] using
          patsBinds_eval ρ ps pl.child fs bs (fun j w hj => Place.eval_child hv hj) hm
      · simp [Pat.matchVal, ht] at hm

theorem patsBinds_eval (ρ : Env) : ∀ (ps : List Pat) (mk : Nat → Place) (vs bs : List Value),
    (∀ j v, vs[j]? = some v → (mk j).eval ρ = some v) → Pat.matchVals ps vs = some bs →
    evalPlaces ρ (patsBinds ps mk) = some bs
  | [], _, vs, _, _, hm => by
    cases vs with
    | nil =>
      simp [Pat.matchVals] at hm
      subst hm
      simp [patsBinds, evalPlaces]
    | cons v vs => simp [Pat.matchVals] at hm
  | p :: ps, mk, vs, _, hmk, hm => by
    cases vs with
    | nil => simp [Pat.matchVals] at hm
    | cons v vs =>
      cases hp : p.matchVal v with
      | none => simp [Pat.matchVals, hp] at hm
      | some b =>
        cases hps : Pat.matchVals ps vs with
        | none => simp [Pat.matchVals, hp, hps] at hm
        | some bs' =>
          simp [Pat.matchVals, hp, hps] at hm
          subst hm
          have ih₁ := patBinds_eval ρ p (mk 0) v b (hmk 0 v (by simp)) hp
          have ih₂ := patsBinds_eval ρ ps (fun j => mk (j + 1)) vs bs'
            (fun j w hj => hmk (j + 1) w (by simpa using hj)) hps
          rw [patsBinds]
          exact evalPlaces_append ih₁ ih₂

end

/-! ## How the machine executes them -/

section Machine

variable {P : Bytecode.Program} {code : Code} {fr : List Bytecode.Frame}
  {ks : Store Bytecode.Frame}

theorem step_test_pass {ρ : Env} {pc : Nat} {t : Test} {fail : Nat}
    (hi : code[pc]? = some (Test.instr fail t)) (hb : t.check ρ = some true) :
    Bytecode.step P ⟨code, pc, ρ, fr, ks⟩ = .next ⟨code, pc + 1, ρ, fr, ks⟩ := by
  cases t with
  | ctor pl tag arity =>
    simp only [Test.instr] at hi
    simp only [Test.check] at hb
    cases hv : pl.eval ρ with
    | none => simp [hv] at hb
    | some v =>
      simp [hv] at hb
      simp [Bytecode.step, hi, hv, hb]
  | int pl n =>
    simp only [Test.instr] at hi
    simp only [Test.check] at hb
    cases hv : pl.eval ρ with
    | none => simp [hv] at hb
    | some v =>
      simp [hv] at hb
      simp [Bytecode.step, hi, hv, hb]

theorem step_test_fail {ρ : Env} {pc : Nat} {t : Test} {fail : Nat}
    (hi : code[pc]? = some (Test.instr fail t)) (hb : t.check ρ = some false) :
    Bytecode.step P ⟨code, pc, ρ, fr, ks⟩ = .next ⟨code, fail, ρ, fr, ks⟩ := by
  cases t with
  | ctor pl tag arity =>
    simp only [Test.instr] at hi
    simp only [Test.check] at hb
    cases hv : pl.eval ρ with
    | none => simp [hv] at hb
    | some v =>
      simp [hv] at hb
      simp [Bytecode.step, hi, hv, hb]
  | int pl n =>
    simp only [Test.instr] at hi
    simp only [Test.check] at hb
    cases hv : pl.eval ρ with
    | none => simp [hv] at hb
    | some v =>
      simp [hv] at hb
      simp [Bytecode.step, hi, hv, hb]

/-- Tests that all hold fall through, one instruction each. -/
theorem tests_pass {ρ : Env} {fail : Nat} {rest : Code} : ∀ (ts : List Test) (pc : Nat),
    checkAll ρ ts = some true → CodeAt code pc (ts.map (Test.instr fail) ++ rest) →
    run (Bytecode.step P) ts.length ⟨code, pc, ρ, fr, ks⟩ = .next ⟨code, pc + ts.length, ρ, fr, ks⟩ := by
  intro ts
  induction ts with
  | nil => intro pc _ _; rfl
  | cons t ts ih =>
    intro pc h hc
    have hc' : CodeAt code pc (Test.instr fail t :: (ts.map (Test.instr fail) ++ rest)) := hc
    cases hb : t.check ρ with
    | none => simp [checkAll, hb] at h
    | some r =>
      cases r with
      | false => simp [checkAll, hb] at h
      | true =>
        simp [checkAll, hb] at h
        have e : pc + (t :: ts).length = pc + 1 + ts.length := by
          simp only [List.length_cons]; omega
        rw [e, List.length_cons, run_succ, step_test_pass hc'.head hb, Step.bind_next]
        exact ih (pc + 1) h hc'.tail

/-- Tests of which one fails jump to the failure target, leaving the locals untouched. -/
theorem tests_fail {ρ : Env} {fail : Nat} {rest : Code} : ∀ (ts : List Test) (pc : Nat),
    checkAll ρ ts = some false → CodeAt code pc (ts.map (Test.instr fail) ++ rest) →
    ∃ k, run (Bytecode.step P) (k + 1) ⟨code, pc, ρ, fr, ks⟩ = .next ⟨code, fail, ρ, fr, ks⟩ := by
  intro ts
  induction ts with
  | nil => intro pc h _; simp [checkAll] at h
  | cons t ts ih =>
    intro pc h hc
    have hc' : CodeAt code pc (Test.instr fail t :: (ts.map (Test.instr fail) ++ rest)) := hc
    cases hb : t.check ρ with
    | none => simp [checkAll, hb] at h
    | some r =>
      cases r with
      | false => exact ⟨0, run_one_next (step_test_fail hc'.head hb)⟩
      | true =>
        simp [checkAll, hb] at h
        obtain ⟨k, hk⟩ := ih (pc + 1) h hc'.tail
        refine ⟨k + 1, ?_⟩
        rw [run_succ, step_test_pass hc'.head hb, Step.bind_next]
        exact hk

/-- Loading the bound places appends exactly the bound values. -/
theorem binds_run {ρ : Env} {rest : Code} :
    ∀ (pls : List Place) (bs extra : List Value) (pc : Nat), evalPlaces ρ pls = some bs →
    CodeAt code pc (pls.map (fun pl => Instr.op (.place pl)) ++ rest) →
    run (Bytecode.step P) pls.length ⟨code, pc, ρ ++ extra, fr, ks⟩
      = .next ⟨code, pc + pls.length, ρ ++ extra ++ bs, fr, ks⟩ := by
  intro pls
  induction pls with
  | nil =>
    intro bs extra pc h _
    simp [evalPlaces] at h
    subst h
    simp
  | cons pl pls ih =>
    intro bs extra pc h hc
    have hc' : CodeAt code pc
        (Instr.op (.place pl) :: (pls.map (fun pl => Instr.op (.place pl)) ++ rest)) := hc
    simp only [evalPlaces] at h
    cases hp : pl.eval ρ with
    | none => simp [hp] at h
    | some v =>
      cases hr : evalPlaces ρ pls with
      | none => simp [hp, hr] at h
      | some vs =>
        simp [hp, hr] at h
        subst h
        have hstep : Bytecode.step P ⟨code, pc, ρ ++ extra, fr, ks⟩
            = .next ⟨code, pc + 1, ρ ++ extra ++ [v], fr, ks⟩ := by
          simp [Bytecode.step, hc'.head, Rhs.eval, Place.eval_append hp]
        have hrest := ih vs (extra ++ [v]) (pc + 1) hr hc'.tail
        have e : pc + (pl :: pls).length = pc + 1 + pls.length := by
          simp only [List.length_cons]; omega
        rw [e, List.length_cons, run_succ, hstep, Step.bind_next]
        simpa [List.append_assoc] using hrest

theorem compileClause_length (fail : Nat) (c : Core.Clause) :
    (compileClause fail c).length = clauseLen c := by
  simp only [compileClause, clauseLen, List.length_append, List.length_map]

/--
Entering a callable's code with the arguments in place runs to the body of the
clause the Core semantics selects, with that clause's bindings appended.
-/
theorem select_run {ρ : Env} {vs : List Value} {body : Core.Tm} {bs : List Value}
    (hargs : ∀ j v, vs[j]? = some v → (argPlace j).eval ρ = some v) :
    ∀ (cs : List Core.Clause) (pc : Nat), Core.selectClause cs vs = some (body, bs) →
    CodeAt code pc (compileClauses pc cs) →
    ∃ k pc', run (Bytecode.step P) k ⟨code, pc, ρ, fr, ks⟩ = .next ⟨code, pc', ρ ++ bs, fr, ks⟩
      ∧ CodeAt code pc' (compileTm body) := by
  intro cs
  induction cs with
  | nil => intro pc h _; simp [Core.selectClause] at h
  | cons c cs ih =>
    intro pc h hc
    simp only [Core.selectClause] at h
    have hc0 : CodeAt code pc
        (compileClause (pc + clauseLen c) c ++ compileClauses (pc + clauseLen c) cs) := hc
    have hcT : CodeAt code pc
        ((clauseTests c).map (Test.instr (pc + clauseLen c))
          ++ ((clauseBinds c).map (fun pl => Instr.op (.place pl)) ++ compileTm c.body)) := by
      simpa [compileClause, List.append_assoc] using hc0.append_left
    by_cases hlen : c.pats.length = vs.length
    · have hcheck := patsTests_check ρ c.pats argPlace vs hlen hargs
      cases hm : Pat.matchVals c.pats vs with
      | none =>
        simp [hlen, hm] at h
        have hfalse : checkAll ρ (clauseTests c) = some false := by
          simpa [clauseTests, hm] using hcheck
        have hnext : CodeAt code (pc + clauseLen c) (compileClauses (pc + clauseLen c) cs) := by
          have := hc0.append_right
          rwa [compileClause_length] at this
        obtain ⟨k, hk⟩ := tests_fail (P := P) (fr := fr) (ks := ks) (clauseTests c) pc hfalse hcT
        obtain ⟨k', pc', hk', hbody⟩ := ih (pc + clauseLen c) h hnext
        refine ⟨(k + 1) + k', pc', ?_, hbody⟩
        rw [run_add, hk, Step.bind_next]
        exact hk'
      | some bs' =>
        simp [hlen, hm] at h
        obtain ⟨rfl, rfl⟩ := h
        have htrue : checkAll ρ (clauseTests c) = some true := by
          simpa [clauseTests, hm] using hcheck
        have hbinds : evalPlaces ρ (clauseBinds c) = some bs' :=
          patsBinds_eval ρ c.pats argPlace vs bs' hargs hm
        have h1 := tests_pass (P := P) (fr := fr) (ks := ks) (clauseTests c) pc htrue hcT
        have hcB : CodeAt code (pc + (clauseTests c).length)
            ((clauseBinds c).map (fun pl => Instr.op (.place pl)) ++ compileTm c.body) := by
          simpa using hcT.append_right
        have h2 := binds_run (P := P) (fr := fr) (ks := ks) (clauseBinds c) bs' [] _ hbinds hcB
        have hcBody : CodeAt code (pc + (clauseTests c).length + (clauseBinds c).length)
            (compileTm c.body) := by
          simpa using hcB.append_right
        refine ⟨(clauseTests c).length + (clauseBinds c).length, _, ?_, hcBody⟩
        rw [run_add, h1, Step.bind_next]
        simpa using h2
    · simp [hlen] at h

end Machine

end Glorious
