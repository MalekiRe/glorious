import Glorious.Typing.Certify
import Glorious.Proof.Witness

/-!
# A well-typed, well-owned program

The safety theorems would say nothing if the checker accepted no program. Here
it accepts the `effects` program of `Glorious.Witness`, with the ownership
rules on: the program installs three handlers, performs a resumptive operation
under a handler that does not serve it, resumes each resumption once, and ends
with a terminal operation. The kernel runs the checker to confirm it.
-/

namespace Glorious.Typing.Witness

open Core

/-- `Ask`, operation 0. -/
def askRow : Row := [(0, [])]

/-- `Fail`, operation 1. -/
def failRow : Row := [(1, [])]

/-- A computation that may ask; it can be run any number of times. -/
def asker : Ty := .fn [] .int askRow false

/-- The resumption the `Ask` arm receives: it runs where `Fail` is served, and
can be resumed once. -/
def resumption : Ty := .fn [.int] .int failRow true

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
  -- `Ask` takes an integer and is resumed with one; `Fail` takes an integer
  -- and is not resumed.
  ops := [⟨0, [], [.int], some .int⟩, ⟨1, [], [.int], none⟩]
  mainTy := .int
  mainHints := [.ty asker, .ty asker, .ty (.fn [] .int failRow false), .handler .int failRow]
  strict := true

theorem effects_checked : checkProgram cert Glorious.Witness.effects = true := by decide

/-- So `effects` is well typed and well owned. -/
theorem effects_ok : ProgramOk cert.ctx Glorious.Witness.effects :=
  checkProgram_sound effects_checked

/-- Given any input, `effects` cannot go wrong except by overflow, a freed cell
or a dead label; and it does not: it halts (`Glorious.Witness.effects_core`). -/
theorem effects_safe (input : List Int) (h : GoesWrong Glorious.Witness.effects input) :
    ∃ c, Machine.Reaches (stepIO Glorious.Witness.effects)
        (initIO Glorious.Witness.effects input) c
      ∧ stepIO Glorious.Witness.effects c = .stuck ∧ Fault c.state ∧ ¬ Resumed c.state :=
  checked_owned_safety effects_checked rfl input h

/-! `resumeTwice` of `Glorious.Witness` resumes one resumption twice. It is well
typed, and goes wrong by exactly the fault the ownership rules are for; with
those rules on, the checker turns it away. -/

def twiceCert (strict : Bool) : Cert where
  sigs := [
    ⟨0, ⟨[], [], .int, askRow⟩, [[]]⟩,
    ⟨1, ⟨[], [.int, .fn [.int] .int [] true], .int, []⟩, [[]]⟩,
    ⟨2, ⟨[], [.int], .int, []⟩, [[]]⟩]
  datas := []
  ops := [⟨0, [], [.int], some .int⟩]
  mainTy := .int
  mainHints := [.ty asker, .handler .int askRow]
  strict := strict

example : checkProgram (twiceCert false) Glorious.Witness.resumeTwice = true := by decide

example : checkProgram (twiceCert true) Glorious.Witness.resumeTwice = false := by decide

/-! What the checker turns away, and a use of the coverage check on a data type. -/

/-- Reading a local that does not exist. -/
example : checkProgram ⟨[], [], [], .int, [], true⟩ ⟨[], .ret (.var 0)⟩ = false := by decide

/-- Performing an operation nothing handles. -/
example : checkProgram ⟨[], [], [], .int, [], true⟩ ⟨[], .raise 0 []⟩ = false := by decide

/-- Calling something that is not callable. -/
example : checkProgram ⟨[], [], [], .int, [.ty .int], true⟩
    ⟨[], .let_ (.atom (.int 1)) (.tail (.var 0) [])⟩ = false := by decide

/-- A function with a clause for `0` only does not cover its integer parameter;
with a second clause that binds the argument, it does. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [.int], .int, []⟩, [[]]⟩], [], [], .int, [.ty (.fn [.int] .int [] false)], true⟩
    ⟨[⟨[⟨[.int 0], .ret (.int 1)⟩]⟩], .let_ (.closure 0 []) (.tail (.var 0) [.int 5])⟩
    = false := by decide

example : checkProgram
    ⟨[⟨0, ⟨[], [.int], .int, []⟩, [[], []]⟩], [], [], .int,
      [.ty (.fn [.int] .int [] false)], true⟩
    ⟨[⟨[⟨[.int 0], .ret (.int 1)⟩, ⟨[.bind], .ret (.var 1)⟩]⟩],
      .let_ (.closure 0 []) (.tail (.var 0) [.int 5])⟩
    = true := by decide

/-- An option of an integer: `None` is constructor 1, `Some` is constructor 2. -/
def option : Ty := .data 0 []

def optionDecl : DataInst := ⟨0, [], [(1, []), (2, [.int])], true⟩

/-- `get(None) = 0; get(Some(x)) = x`, applied to `Some(7)`: both constructors
have a clause, so the function covers its parameter. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [option], .int, []⟩, [[], []]⟩], [optionDecl], [], .int,
      [.ty option, .ty (.fn [option] .int [] false)], true⟩
    ⟨[⟨[⟨[.ctor 1 []], .ret (.int 0)⟩, ⟨[.ctor 2 [.bind]], .ret (.var 1)⟩]⟩],
      .let_ (.construct 2 [.int 7]) (.let_ (.closure 0 []) (.tail (.var 1) [.var 0]))⟩
    = true := by decide

/-- Without the clause for `None` it does not. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [option], .int, []⟩, [[]]⟩], [optionDecl], [], .int,
      [.ty option, .ty (.fn [option] .int [] false)], true⟩
    ⟨[⟨[⟨[.ctor 2 [.bind]], .ret (.var 1)⟩]⟩],
      .let_ (.construct 2 [.int 7]) (.let_ (.closure 0 []) (.tail (.var 1) [.var 0]))⟩
    = false := by decide

end Glorious.Typing.Witness
