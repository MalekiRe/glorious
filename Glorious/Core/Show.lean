module

public import Glorious.Core.Ast

/-!
# Core, as text

For reading what the elaborator made (`glorious core`, `GLORIOUS_TYPER=core`).
-/

@[expose] public section

namespace Glorious.Core

def showAtom : Atom → String
  | .var i => s!"v{i}"
  | .int n => s!"{n}"

def showAtoms (as : List Atom) : String := ", ".intercalate (as.map showAtom)

def showRhs : Rhs → String
  | .atom a => showAtom a
  | .prim _ args => s!"prim({showAtoms args})"
  | .construct tag args => s!"#{tag}({showAtoms args})"
  | .place pl => s!"v{pl.var}.{pl.path}"
  | .closure fn caps => s!"fn{fn}[{showAtoms caps}]"

partial def showTm (n : Nat) : Core.Tm → String
  | .ret a => s!"ret {showAtom a}"
  | .let_ rhs body => s!"let v{n} = {showRhs rhs}\n" ++ showTm (n + 1) body
  | .call f args body => s!"let v{n} = {showAtom f}({showAtoms args})\n" ++ showTm (n + 1) body
  | .tail f args => s!"tail {showAtom f}({showAtoms args})"
  | .handle _ _ caps thunk body =>
    s!"let v{n} = handle {showAtom thunk} [{showAtoms caps}]\n" ++ showTm (n + 1) body
  | .handleTail _ _ caps thunk => s!"handle {showAtom thunk} [{showAtoms caps}]"
  | .raise op args => s!"raise op{op}({showAtoms args})"
  | .perform op args body => s!"let v{n} = perform op{op}({showAtoms args})\n" ++ showTm (n + 1) body
  | .label thunk body => s!"let v{n} = label {showAtom thunk}\n" ++ showTm (n + 1) body
  | .labelTail thunk => s!"label {showAtom thunk}"
  | .guard c thunk body => s!"let v{n} = guard {showAtom c} {showAtom thunk}\n" ++ showTm (n + 1) body
  | .guardTail c thunk => s!"guard {showAtom c} {showAtom thunk}"
  | .cancel k body => s!"let v{n} = cancel {showAtom k}\n" ++ showTm (n + 1) body
  | .cell init thunk body => s!"let v{n} = cell {showAtom init} in {showAtom thunk}\n" ++ showTm (n + 1) body
  | .cellTail init thunk => s!"cell {showAtom init} in {showAtom thunk}"
  | .cellL l init thunk body => s!"let v{n} = cell[{l.size}] {showAtom init} in {showAtom thunk}\n" ++ showTm (n + 1) body
  | .cellTailL l init thunk => s!"cell[{l.size}] {showAtom init} in {showAtom thunk}"
  | .lend u r thunk pre post body =>
    s!"let v{n} = lend{if u then " mut" else ""} {showAtom r} to {showAtom thunk}({showAtoms pre} | {showAtoms post})\n"
      ++ showTm (n + 1) body
  | .mem _ args body => s!"let v{n} = mem({showAtoms args})\n" ++ showTm (n + 1) body
  | .host id args body => s!"let v{n} = host{id}({showAtoms args})\n" ++ showTm (n + 1) body


partial def showPat : Core.Pat → String
  | .wild => "_"
  | .bind => "x"
  | .int n => s!"{n}"
  | .ctor tag ps => s!"#{tag}(" ++ ", ".intercalate (ps.map showPat) ++ ")"

/-- How many locals a pattern binds. -/
partial def Pat.binds : Core.Pat → Nat
  | .bind => 1
  | .ctor _ ps => (ps.map Pat.binds).sum
  | _ => 0

/-- How many values each function is made with, where it is made. -/
partial def capsAt : Core.Tm → List (Nat × Nat)
  | .let_ (.closure f cs) b => (f, cs.length) :: capsAt b
  | .let_ _ b | .call _ _ b | .perform _ _ b | .label _ b | .guard _ _ b | .cancel _ b
  | .cell _ _ b | .cellL _ _ _ b | .lend _ _ _ _ _ b | .mem _ _ b | .host _ _ b => capsAt b
  | .handle ret ops cs _ b => (ret :: ops.map (·.2)).map (·, cs.length) ++ capsAt b
  | .handleTail ret ops cs _ => (ret :: ops.map (·.2)).map (·, cs.length)
  | _ => []

/-- A program's Core, each local numbered as it is. -/
def showCore (names : Array String) (p : Core.Program) : String := Id.run do
  let caps := (p.main :: p.fns.toList.flatMap (·.clauses.map (·.body))).flatMap capsAt
  let mut out := ""
  for (F, i) in p.fns.zipIdx do
    out := out ++ s!"fn{i} {names[i]?.getD ""}:\n"
    let ncaps := (caps.lookup i).getD 0
    for c in F.clauses do
      out := out ++ s!"  clause ({", ".intercalate (c.pats.map showPat)}) [{ncaps} captured]\n"
      let lines := (showTm (c.pats.length + ncaps + (c.pats.map Pat.binds).sum) c.body).splitOn "\n"
      for l in lines do
        out := out ++ s!"    {l}\n"
  out ++ "main:\n" ++ "\n".intercalate (((showTm 0 p.main).splitOn "\n").map ("  " ++ ·))

end Glorious.Core
