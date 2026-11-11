/-!
# Runtime values and operands

Core and bytecode share one notion of runtime value and one notion of operand.
An activation's environment only grows, so an operand names a local by its
position in that environment.
-/

namespace Glorious

/-- A runtime value. -/
inductive Value where
  /-- An integer. Arithmetic keeps it within 64 bits; see `checked`. -/
  | int (n : Int)
  /-- A `struct` or `enum` value: a constructor tag and its fields. -/
  | data (tag : Nat) (fields : List Value)
  /-- A callable: the index of its function and the values it captured. -/
  | clo (fn : Nat) (captures : List Value)
  /-- A resumption: the identity of a captured continuation. -/
  | cont (id : Nat)
  /-- A label: the identity of a label scope. -/
  | label (id : Nat)
  /-- A reference: the address of a memory cell, and which borrow of the cell
  it is. The cell's own reference is borrow zero. Nothing the machine does
  depends on the borrow: it is there so that what it means for a borrow to be
  respected can be said. -/
  | ref (addr : Nat) (borrow : Nat)

/-- The locals of one activation, oldest first. -/
abbrev Env := List Value

/-- An operand: something that is already a value once locals are looked up. -/
inductive Atom where
  /-- The local at position `i` of the current environment. -/
  | var (i : Nat)
  | int (n : Int)

/-- A field path into a local: `var.path₀.path₁...`. -/
structure Place where
  var : Nat
  path : List Nat

/-- Machine intrinsics. Their meaning is shared by both machines. -/
inductive Prim where
  | intAdd
  | intSub
  | intMul
  /-- `1` if the first integer is smaller, else `0`. -/
  | intLt
  /-- `1` if the integers are equal, else `0`. -/
  | intEq

/-- A computation that produces a value without transferring control. -/
inductive Rhs where
  | atom (a : Atom)
  | prim (p : Prim) (args : List Atom)
  | construct (tag : Nat) (args : List Atom)
  /-- Read a field path out of a local. -/
  | place (pl : Place)
  | closure (fn : Nat) (captures : List Atom)
  /-- What a closure captured, under the code of another function: the closure
  `a` is given up and `fn` runs in its place. -/
  | rebind (a : Atom) (fn : Nat)

namespace Value

/-- The unit value: the empty tuple. -/
def unit : Value := .data 0 []

/-- Follow a field path into a value. -/
def follow : Value → List Nat → Option Value
  | v, [] => some v
  | .data _ fields, i :: path =>
    match fields[i]? with
    | some field => field.follow path
    | none => none
  | .int _, _ :: _ => none
  | .clo _ _, _ :: _ => none
  | .cont _, _ :: _ => none
  | .label _, _ :: _ => none
  | .ref _ _, _ :: _ => none

/-- Is this value built by constructor `tag` with exactly `arity` fields? -/
def isCtor (v : Value) (tag arity : Nat) : Bool :=
  match v with
  | .data t fields => tag == t && arity == fields.length
  | .int _ => false
  | .clo _ _ => false
  | .cont _ => false
  | .label _ => false
  | .ref _ _ => false

/-- Is this value the integer `n`? -/
def isInt (v : Value) (n : Int) : Bool :=
  match v with
  | .int m => n == m
  | .data _ _ => false
  | .clo _ _ => false
  | .cont _ => false
  | .label _ => false
  | .ref _ _ => false

end Value

namespace Place

def eval (ρ : Env) (pl : Place) : Option Value :=
  match ρ[pl.var]? with
  | some v => v.follow pl.path
  | none => none

/-- The place of field `i` of this place. -/
def child (pl : Place) (i : Nat) : Place := ⟨pl.var, pl.path ++ [i]⟩

end Place

/-- Integers are 64-bit and arithmetic is checked: a result outside this range
has no meaning. -/
def checked (n : Int) : Option Value :=
  if -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 then some (.int n) else none

def Prim.eval : Prim → List Value → Option Value
  | .intAdd, [.int a, .int b] => checked (a + b)
  | .intSub, [.int a, .int b] => checked (a - b)
  | .intMul, [.int a, .int b] => checked (a * b)
  | .intLt, [.int a, .int b] => some (.int (if a < b then 1 else 0))
  | .intEq, [.int a, .int b] => some (.int (if a = b then 1 else 0))
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
  | .place pl => pl.eval ρ
  | .closure fn captures =>
    match evalAtoms ρ captures with
    | some vs => some (.clo fn vs)
    | none => none
  | .rebind a fn =>
    match a.eval ρ with
    | some (.clo _ captured) => some (.clo fn captured)
    | _ => none

end Glorious
