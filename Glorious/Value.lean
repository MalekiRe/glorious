/-!
# Runtime values and operands

Core and bytecode share one notion of runtime value and one notion of operand.
An activation's environment only grows, so an operand names a local by its
position in that environment.
-/

namespace Glorious

/-- A runtime value. -/
inductive Value where
  /-- A mathematical integer. Fixed-width arithmetic is not modelled yet. -/
  | int (n : Int)
  /-- A `struct` or `enum` value: a constructor tag and its fields. -/
  | data (tag : Nat) (fields : List Value)
  /-- A callable: the index of its function and the values it captured. -/
  | clo (fn : Nat) (captures : List Value)

/-- The locals of one activation, oldest first. -/
abbrev Env := List Value

/-- An operand: something that is already a value once locals are looked up. -/
inductive Atom where
  /-- The local at position `i` of the current environment. -/
  | var (i : Nat)
  | int (n : Int)

/-- Machine intrinsics. Their meaning is shared by both machines. -/
inductive Prim where
  | intAdd
  | intSub
  | intMul

/-- A computation that produces a value without transferring control. -/
inductive Rhs where
  | atom (a : Atom)
  | prim (p : Prim) (args : List Atom)
  | construct (tag : Nat) (args : List Atom)
  | project (a : Atom) (idx : Nat)
  | closure (fn : Nat) (captures : List Atom)

def Prim.eval : Prim → List Value → Option Value
  | .intAdd, [.int a, .int b] => some (.int (a + b))
  | .intSub, [.int a, .int b] => some (.int (a - b))
  | .intMul, [.int a, .int b] => some (.int (a * b))
  | _, _ => none

def Atom.eval (ρ : Env) : Atom → Option Value
  | .var i => ρ[i]?
  | .int n => some (.int n)

def evalAtoms (ρ : Env) : List Atom → Option (List Value)
  | [] => some []
  | a :: as =>
    match a.eval ρ, evalAtoms ρ as with
    | some v, some vs => some (v :: vs)
    | _, _ => none

def Rhs.eval (ρ : Env) : Rhs → Option Value
  | .atom a => a.eval ρ
  | .prim p args =>
    match evalAtoms ρ args with
    | some vs => p.eval vs
    | none => none
  | .construct tag args =>
    match evalAtoms ρ args with
    | some vs => some (.data tag vs)
    | none => none
  | .project a idx =>
    match a.eval ρ with
    | some (.data _ fields) => fields[idx]?
    | _ => none
  | .closure fn captures =>
    match evalAtoms ρ captures with
    | some vs => some (.clo fn vs)
    | none => none

/-- Evaluate the callee and arguments of a call: the function index, the
captured values and the argument values. -/
def evalCall (ρ : Env) (f : Atom) (args : List Atom) : Option (Nat × List Value × List Value) :=
  match f.eval ρ, evalAtoms ρ args with
  | some (.clo fn captures), some vs => some (fn, captures, vs)
  | _, _ => none

end Glorious
