import Glorious.Typing.Certify
import Glorious.Proof.Witness

/-!
# A well-typed program

`type_safety` would say nothing if no program were well typed. Here the
`effects` program of `Glorious.Witness` is typed: it installs three handlers,
performs a resumptive operation under a handler that does not serve it, resumes
each resumption once, and ends with a terminal operation.
-/

namespace Glorious.Typing.Witness

open Core

/-- `Ask`: takes an integer and is resumed with one. -/
def askRow : Row := [(0, [])]

/-- `Fail`: takes an integer and is not resumed. -/
def failRow : Row := [(1, [])]

/-- A computation that may ask. -/
def asker : Ty := .fn [] .int askRow

/-- The resumption the `Ask` arm receives: it runs where `Fail` is served. -/
def resumption : Ty := .fn [.int] .int failRow

def sigs : List (Nat × FnSig) := [
  (0, ⟨[], [], .int, askRow⟩),
  (1, ⟨[], [.int, resumption], .int, failRow⟩),
  (2, ⟨[], [.int], .int, []⟩),
  (3, ⟨[], [.int], .int, []⟩),
  (4, ⟨[], [.int], .int, []⟩),
  (5, ⟨[asker], [], .int, askRow⟩),
  (6, ⟨[asker], [], .int, failRow⟩)]

/-- Each function of `effects` has one signature; `Ask` takes an integer and is
resumed with one, `Fail` takes an integer and is not resumed; and the program
declares no data types. -/
def ctx : Ctx where
  fnSig fn sig := (fn, sig) ∈ sigs
  opSig op _ := if op = 0 then some ([.int], some .int) else if op = 1 then some ([.int], none) else none
  ctorFields _ _ _ := none

theorem sig0 : ctx.fnSig 0 ⟨[], [], .int, askRow⟩ := .head _
theorem sig1 : ctx.fnSig 1 ⟨[], [.int, resumption], .int, failRow⟩ := .tail _ (.head _)
theorem sig2 : ctx.fnSig 2 ⟨[], [.int], .int, []⟩ := .tail _ (.tail _ (.head _))
theorem sig3 : ctx.fnSig 3 ⟨[], [.int], .int, []⟩ := .tail _ (.tail _ (.tail _ (.head _)))
theorem sig4 : ctx.fnSig 4 ⟨[], [.int], .int, []⟩ :=
  .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
theorem sig5 : ctx.fnSig 5 ⟨[asker], [], .int, askRow⟩ :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
theorem sig6 : ctx.fnSig 6 ⟨[asker], [], .int, failRow⟩ :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))

/-- Under the `Fail` handler, `Ask` is still the enclosing handler's. -/
theorem ask_under_fail : Row.le askRow (failRow ++ askRow) := by
  intro op sig h
  by_cases h0 : op = 0
  · subst h0
    exact h
  · rw [show askRow = [(0, [])] from rfl, lookup_cons_ne h0] at h
    simp [List.lookup] at h

/-- The handler that serves `Fail` by adding one, used twice. -/
theorem failHandler (ε : Row) : HandlerOk ctx [] 3 [(1, 4)] .int .int failRow ε :=
  ⟨⟨[], sig3, Row.nil_le _⟩, .terminal (targs := []) (Ps := [.int]) (εa := []) rfl sig4 (Row.nil_le _) .nil⟩

/-- A function of no arguments has a clause for no arguments. -/
theorem covers0 {S : StoreTy} {body : Tm} {vs : List Value} (h : HasVals ctx S vs []) :
    selectClause [⟨[], body⟩] vs ≠ none := by
  cases h
  simp [selectClause, Pat.matchVals]

theorem covers1 {S : StoreTy} {body : Tm} {vs : List Value} {τ : Ty}
    (h : HasVals ctx S vs [τ]) : selectClause [⟨[.wild], body⟩] vs ≠ none := by
  cases h with
  | cons _ h =>
    cases h
    simp [selectClause, Pat.matchVals, Pat.matchVal]

theorem covers2 {S : StoreTy} {body : Tm} {vs : List Value} {τ σ : Ty}
    (h : HasVals ctx S vs [τ, σ]) : selectClause [⟨[.wild, .wild], body⟩] vs ≠ none := by
  cases h with
  | cons _ h =>
    cases h with
    | cons _ h =>
      cases h
      simp [selectClause, Pat.matchVals, Pat.matchVal]

/-- The `effects` program is well typed. -/
theorem effects_ok : ProgramOk ctx Glorious.Witness.effects where
  fns := by
    intro fn sig h
    simp only [ctx, sigs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩
    · refine ⟨_, rfl, ?_, fun S vs hv => covers0 hv⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨[], .nil,
        .perform (targs := []) (Ps := [.int]) (σ := .int) rfl rfl (.cons .int .nil)
          (.perform (targs := []) (Ps := [.int]) (σ := .int) rfl rfl (.cons (.var rfl) .nil)
            (.let_ (σ := .int) (.prim (.var rfl) (.var rfl)) (.ret (.var rfl))))⟩
    · refine ⟨_, rfl, ?_, fun S vs hv => covers2 hv⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨[], .cons .wild (.cons .wild .nil),
        .let_ (σ := .int) (.prim (.var rfl) .int)
          (.tail (Ps := [.int]) (ε' := failRow) (.var rfl) (.cons (.var rfl) .nil)
            (Row.le_refl _))⟩
    · refine ⟨_, rfl, ?_, fun S vs hv => covers1 hv⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨[], .cons .wild .nil,
        .let_ (σ := .int) (.prim (.var rfl) .int) (.ret (.var rfl))⟩
    · refine ⟨_, rfl, ?_, fun S vs hv => covers1 hv⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨[], .cons .wild .nil, .ret (.var rfl)⟩
    · refine ⟨_, rfl, ?_, fun S vs hv => covers1 hv⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨[], .cons .wild .nil,
        .let_ (σ := .int) (.prim (.var rfl) .int) (.ret (.var rfl))⟩
    · refine ⟨_, rfl, ?_, fun S vs hv => covers0 hv⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨[], .nil,
        .handle (Cs := []) (σ := .int) (ρ := .int) (εt := askRow) (H := failRow) (.var rfl) .nil
          (failHandler _) ask_under_fail (.ret (.var rfl))⟩
    · refine ⟨_, rfl, ?_, fun S vs hv => covers0 hv⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨[], .nil,
        .handle (Cs := []) (σ := .int) (ρ := .int) (εt := askRow) (H := askRow) (.var rfl) .nil
          ⟨⟨[], sig2, Row.nil_le _⟩,
            .resumptive (targs := []) (Ps := [.int]) (o := .int) (εa := failRow) rfl sig1
              (Row.le_refl _) .nil⟩
          (Row.le_append_left _ _)
          (.raise (targs := []) (Ps := [.int]) rfl rfl (.cons (.var rfl) .nil))⟩
  main := ⟨.int,
    .let_ (σ := asker) (.closure (sig := ⟨[], [], .int, askRow⟩) sig0 .nil)
      (.let_ (σ := asker)
        (.closure (sig := ⟨[asker], [], .int, askRow⟩) sig5 (.cons (.var rfl) .nil))
        (.let_ (σ := .fn [] .int failRow)
          (.closure (sig := ⟨[asker], [], .int, failRow⟩) sig6 (.cons (.var rfl) .nil))
          (.handle (Cs := []) (σ := .int) (ρ := .int) (εt := failRow) (H := failRow)
            (.var rfl) .nil (failHandler _) (Row.le_append_left _ _) (.ret (.var rfl)))))⟩

/-- So `effects`, given any input, cannot go wrong except by a fault; and it
does not: it halts (`Glorious.Witness.effects_core`). -/
theorem effects_safe (input : List Int) (h : GoesWrong Glorious.Witness.effects input) :
    ∃ c, Machine.Reaches (stepIO Glorious.Witness.effects)
        (initIO Glorious.Witness.effects input) c
      ∧ stepIO Glorious.Witness.effects c = .stuck ∧ Fault c.state :=
  type_safety effects_ok input h

/-! The same program through the checker: a certificate, and the kernel running
the checker on it. -/

def cert : Cert where
  sigs := [
    ⟨0, ⟨[], [], .int, askRow⟩, [[.ty .int]]⟩,
    ⟨1, ⟨[], [.int, resumption], .int, failRow⟩, [[.ty .int]]⟩,
    ⟨2, ⟨[], [.int], .int, []⟩, [[.ty .int]]⟩,
    ⟨3, ⟨[], [.int], .int, []⟩, [[]]⟩,
    ⟨4, ⟨[], [.int], .int, []⟩, [[.ty .int]]⟩,
    ⟨5, ⟨[asker], [], .int, askRow⟩, [[.handler .int failRow]]⟩,
    ⟨6, ⟨[asker], [], .int, failRow⟩, [[.handler .int askRow]]⟩]
  datas := []
  ops := [⟨0, [], [.int], some .int⟩, ⟨1, [], [.int], none⟩]
  mainTy := .int
  mainHints := [.ty asker, .ty asker, .ty (.fn [] .int failRow), .handler .int failRow]

theorem effects_checked : checkProgram cert Glorious.Witness.effects = true := by decide

/-! What the checker turns away, and a use of the coverage check on a data type. -/

/-- Reading a local that does not exist. -/
example : checkProgram ⟨[], [], [], .int, []⟩ ⟨[], .ret (.var 0)⟩ = false := by decide

/-- Performing an operation nothing handles. -/
example : checkProgram ⟨[], [], [], .int, []⟩ ⟨[], .raise 0 []⟩ = false := by decide

/-- Calling something that is not callable. -/
example : checkProgram ⟨[], [], [], .int, [.ty .int]⟩
    ⟨[], .let_ (.atom (.int 1)) (.tail (.var 0) [])⟩ = false := by decide

/-- A function with a clause for `0` only does not cover its integer parameter;
with a second clause that binds the argument, it does. -/
example : checkProgram ⟨[⟨0, ⟨[], [.int], .int, []⟩, [[]]⟩], [], [], .int, [.ty (.fn [.int] .int [])]⟩
    ⟨[⟨[⟨[.int 0], .ret (.int 1)⟩]⟩], .let_ (.closure 0 []) (.tail (.var 0) [.int 5])⟩
    = false := by decide

example : checkProgram
    ⟨[⟨0, ⟨[], [.int], .int, []⟩, [[], []]⟩], [], [], .int, [.ty (.fn [.int] .int [])]⟩
    ⟨[⟨[⟨[.int 0], .ret (.int 1)⟩, ⟨[.bind], .ret (.var 1)⟩]⟩],
      .let_ (.closure 0 []) (.tail (.var 0) [.int 5])⟩
    = true := by decide

/-- An option of an integer: `None` is constructor 1, `Some` is constructor 2. -/
def option : Ty := .data 0 []

def optionDecl : DataInst := ⟨0, [], [(1, []), (2, [.int])]⟩

/-- `get(None) = 0; get(Some(x)) = x`, applied to `Some(7)`: both constructors
have a clause, so the function covers its parameter. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [option], .int, []⟩, [[], []]⟩], [optionDecl], [], .int,
      [.ty option, .ty (.fn [option] .int [])]⟩
    ⟨[⟨[⟨[.ctor 1 []], .ret (.int 0)⟩, ⟨[.ctor 2 [.bind]], .ret (.var 1)⟩]⟩],
      .let_ (.construct 2 [.int 7]) (.let_ (.closure 0 []) (.tail (.var 1) [.var 0]))⟩
    = true := by decide

/-- Without the clause for `None` it does not. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [option], .int, []⟩, [[]]⟩], [optionDecl], [], .int,
      [.ty option, .ty (.fn [option] .int [])]⟩
    ⟨[⟨[⟨[.ctor 2 [.bind]], .ret (.var 1)⟩]⟩],
      .let_ (.construct 2 [.int 7]) (.let_ (.closure 0 []) (.tail (.var 1) [.var 0]))⟩
    = false := by decide

end Glorious.Typing.Witness
