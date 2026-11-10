import Glorious.Core.Ast
import Glorious.Bytecode.Ast

/-!
# The compiler: Core to bytecode

A computation becomes straight-line code. A callable becomes its clauses laid
out one after another; each clause first tests its patterns, jumping to the
next clause on a mismatch, then loads its bindings, then runs its body.
-/

namespace Glorious

open Bytecode (Instr Code)

/-- Lay a Core computation out as straight-line code. -/
def compileTm : Core.Tm → Code
  | .ret a => [.ret a]
  | .let_ rhs body => .op rhs :: compileTm body
  | .call f args body => .call f args :: compileTm body
  | .tail f args => [.tail f args]
  | .handle ret ops captures thunk body => .handle ret ops captures thunk :: compileTm body
  | .raise op args => [.raise op args]
  | .perform op args body => .perform op args :: compileTm body
  | .label thunk body => .label thunk :: compileTm body
  | .handleTail ret ops captures thunk => [.handleTail ret ops captures thunk]
  | .labelTail thunk => [.labelTail thunk]
  | .host id args body => .host id args :: compileTm body

/-- A structural test a pattern imposes on a place. -/
inductive Test where
  | ctor (pl : Place) (tag arity : Nat)
  | int (pl : Place) (n : Int)

/-- The instruction performing a test, jumping to `fail` when it does not hold. -/
def Test.instr (fail : Nat) : Test → Instr
  | .ctor pl tag arity => .testCtor pl tag arity fail
  | .int pl n => .testInt pl n fail

mutual

/-- The tests a pattern imposes on the value at `pl`, outermost first. -/
def patTests : Core.Pat → Place → List Test
  | .wild, _ => []
  | .bind, _ => []
  | .int n, pl => [.int pl n]
  | .ctor tag ps, pl => .ctor pl tag ps.length :: patsTests ps pl.child

/-- The tests of a list of patterns, where pattern `j` applies to place `mk j`. -/
def patsTests : List Core.Pat → (Nat → Place) → List Test
  | [], _ => []
  | p :: ps, mk => patTests p (mk 0) ++ patsTests ps (fun j => mk (j + 1))

end

mutual

/-- The places a pattern binds, in binder order. -/
def patBinds : Core.Pat → Place → List Place
  | .wild, _ => []
  | .bind, pl => [pl]
  | .int _, _ => []
  | .ctor _ ps, pl => patsBinds ps pl.child

def patsBinds : List Core.Pat → (Nat → Place) → List Place
  | [], _ => []
  | p :: ps, mk => patBinds p (mk 0) ++ patsBinds ps (fun j => mk (j + 1))

end

/-- Argument `j` of a call is local `j` of the callee. -/
def argPlace (j : Nat) : Place := ⟨j, []⟩

def clauseTests (c : Core.Clause) : List Test := patsTests c.pats argPlace

def clauseBinds (c : Core.Clause) : List Place := patsBinds c.pats argPlace

/-- The code of one clause. All tests run before any binding is loaded, so a
failed clause leaves the locals untouched. -/
def compileClause (fail : Nat) (c : Core.Clause) : Code :=
  (clauseTests c).map (Test.instr fail)
    ++ (clauseBinds c).map (fun pl => Instr.op (.place pl))
    ++ compileTm c.body

/-- The length of a clause's code; it does not depend on the jump target. -/
def clauseLen (c : Core.Clause) : Nat :=
  (clauseTests c).length + (clauseBinds c).length + (compileTm c.body).length

/-- Lay clauses out from position `base`. A failed clause jumps to the start of
the next one; past the last clause there is no code. -/
def compileClauses (base : Nat) : List Core.Clause → Code
  | [] => []
  | c :: cs =>
    compileClause (base + clauseLen c) c ++ compileClauses (base + clauseLen c) cs

def compileFn (f : Core.Fn) : Bytecode.Fn := ⟨compileClauses 0 f.clauses⟩

def compile (p : Core.Program) : Bytecode.Program := ⟨p.fns.map compileFn, compileTm p.main⟩

end Glorious
