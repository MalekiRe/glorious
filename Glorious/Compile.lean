import Glorious.Core.Ast
import Glorious.Bytecode.Ast

/-!
# The compiler: Core to bytecode
-/

namespace Glorious

open Bytecode (Instr Code)

/-- Lay a Core computation out as straight-line code. -/
def compileTm : Core.Tm → Code
  | .ret a => [.ret a]
  | .let_ rhs body => .op rhs :: compileTm body
  | .call f args body => .call f args :: compileTm body
  | .tail f args => [.tail f args]

def compileFn (f : Core.Fn) : Bytecode.Fn := ⟨f.arity, compileTm f.body⟩

def compile (p : Core.Program) : Bytecode.Program := ⟨p.fns.map compileFn, compileTm p.main⟩

end Glorious
