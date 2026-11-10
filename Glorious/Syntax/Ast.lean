/-!
# Surface syntax

What the parser produces. Nothing here is trusted: the elaborator turns it into
Core, and Core is what has a semantics.
-/

namespace Glorious.Syntax

/-- A surface pattern. A bare name is a binder unless it resolves to a
constructor or a declared constant. -/
inductive Pattern where
  | wild
  | var (name : String)
  | int (n : Int)
  | ctor (name : String) (qual : Option String) (args : List Pattern)
  | tuple (args : List Pattern)
  deriving Inhabited

mutual

inductive Expr where
  | int (n : Int)
  /-- A variable, function, constructor, operation or constant, optionally qualified. -/
  | name (qual : Option String) (name : String)
  /-- The label `@name` as a value. -/
  | label (name : String)
  | call (f : Expr) (args : List Expr)
  /-- `tail f(args)`. -/
  | tailCall (f : Expr) (args : List Expr)
  | tuple (args : List Expr)
  /-- `e.N`. -/
  | proj (e : Expr) (idx : Nat)
  /-- A callable literal: one or more clauses. A plain block is one clause with no parameters. -/
  | closure (clauses : List Clause)
  /-- `handle subject { arms }`. -/
  | handle (subject : Expr) (arms : List Clause)
  /-- `@name { body }`. -/
  | labelScope (name : String) (body : List Stmt)
  /-- `&x` or `&mut x`: a reference to a mutable variable. -/
  | ref (name : String)
  /-- `*e`: the value a reference points to. -/
  | deref (e : Expr)

inductive Stmt where
  | let_ (pat : Pattern) (value : Expr)
  | expr (e : Expr)
  /-- `defer e;`: run `e` when the rest of the block is left, by any path. -/
  | defer (e : Expr)
  /-- `let mut x = e;`: a variable that can be assigned and borrowed. -/
  | letMut (name : String) (value : Expr)
  /-- `x = e;` or `*p = e;`. -/
  | assign (target : Expr) (value : Expr)

inductive Clause where
  | mk (pats : List Pattern) (body : List Stmt)

end

instance : Inhabited Expr := ⟨.int 0⟩

instance : Inhabited Clause := ⟨.mk [] []⟩

inductive Assoc where
  | left
  | right
  | non

/-- Operator fixities declared by the program. -/
structure Fixities where
  infixes : List (String × Nat × Assoc) := []
  prefixes : List (String × Nat) := []

inductive Item where
  /-- An enum and its constructors with their field counts. -/
  | enum (name : String) (ctors : List (String × Nat))
  /-- A struct with positional fields. -/
  | struct (name : String) (arity : Nat)
  /-- An effect and its operations: name, payload count, and whether it is terminal. -/
  | effect (name : String) (ops : List (String × Nat × Bool))
  | fn (name : String) (clauses : List Clause)
  /-- `let Name = expr;`: a constructor alias or a constant. -/
  | alias (name : String) (value : Expr)
  /-- A fixity declaration; already collected before parsing. -/
  | fixity

end Glorious.Syntax
