module

public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Which implementation a trait bound is met by

A trait is a set of functions a type may have. `impl Trait for Head<T, ...>`
gives them for every type made with `Head`, perhaps on condition that some of
the `T` have traits themselves. A use of one of the functions at a type needs
the implementation for that type, and that is found here, by a function the
checker of the source text calls.

Two things are proved of it. What the function finds is evidence that the bound
is met: `solve_sound`. And a bound is met in at most one way, if no two
implementations are for the same trait and the same head and what a function
may assume of its own type parameters is not said twice: `coherent`. So which
implementation runs does not depend on how it was looked for.

Nothing here knows what a program means. The elaborator turns evidence into a
value, a tuple of the implementation's functions, and passes it where the bound
is needed; that the result is well typed is checked for each program, with the
rest of its Core.
-/

@[expose] public section

namespace Glorious.Traits

-- (The solver is of traits by whatever tells them apart, `κ`: the checker's
-- `Syntax.TraitKey`.)
variable {κ : Type} [BEq κ] [Hashable κ]

/-- A type as far as finding an implementation is concerned: one made with a
name, or one the function being checked is generic in. -/
inductive STy where
  | con (name : String) (args : List STy)
  | var (id : Nat)
  deriving BEq, Hashable

/-- `impl Trait for Head<T0, ..., Tn>`, on condition that each `(trait, i)` in
`context` holds: that `Ti` has that trait. -/
structure Impl (κ : Type) where
  trait : κ
  head : String
  arity : Nat
  context : List (κ × Nat)

/-- The head a tuple of one or more has as its first and the tuple of the
rest: what an implementation for `(H, ..R)` is for, one for every length. -/
def consHead : String := "%Cons"

/-- The head of a tuple of `n`. -/
def tupleHead (n : Nat) : String := s!"(tuple{n})"

/-- The head a function of any number of arguments has, as the tuple of
what it is given and what it gives: what an implementation for `fn(..P) -> R`
is for. -/
def fnHead : String := "%Fn"

/-- The head of a function of `n` arguments (its arguments `n` and its
result). -/
def fnArityHead (n : Nat) : String := s!"(fn{n})"

/-- A type as an implementation for every length sees it, with that head:
a tuple of one or more as its first and the tuple of the rest
(`consHead`); a function as the tuple of what it is given and what it
gives (`fnHead`). -/
def consView : String → List STy → Option (String × List STy)
  | _, [] => none
  | head, a :: rest =>
    if head = tupleHead (rest.length + 1) then some (consHead, [a, .con (tupleHead rest.length) rest])
    else if head = fnArityHead rest.length then
      let all := a :: rest
      some (fnHead, [.con (tupleHead rest.length) all.dropLast, all.getLast (by simp)])
    else none

/-- How a bound is met: by an implementation, given how each of its conditions
is met, or by something the function being checked assumes. -/
inductive Dict where
  | impl (i : Nat) (subs : List Dict)
  | given (k : Nat)

/-- What a function assumes of its own type parameters: each a trait and a type
variable. -/
abbrev Givens (κ : Type) := List (κ × Nat)

mutual

/-- `tr` holds of a type, and this is how. -/
inductive Entails (impls : List (Impl κ)) (givens : Givens κ) : κ → STy → Dict → Prop where
  | given {k : Nat} {tr : κ} {v : Nat} :
      givens[k]? = some (tr, v) → Entails impls givens tr (.var v) (.given k)
  | impl {i : Nat} {I : Impl κ} {tr : κ} {head : String} {args : List STy} {subs : List Dict} :
      impls[i]? = some I → I.trait = tr → I.head = head → I.arity = args.length →
      EntailsAll impls givens I.context args subs →
      Entails impls givens tr (.con head args) (.impl i subs)
  /-- A tuple of one or more by an implementation for its first and the
  rest, a function by one for every number of arguments (`consView`). -/
  | cons {i : Nat} {I : Impl κ} {tr : κ} {head : String} {args args' : List STy} {subs : List Dict} :
      impls[i]? = some I → I.trait = tr → I.arity = 2 →
      consView head args = some (I.head, args') →
      EntailsAll impls givens I.context args' subs →
      Entails impls givens tr (.con head args) (.impl i subs)

/-- Each condition of an implementation holds of the argument it is about. -/
inductive EntailsAll (impls : List (Impl κ)) (givens : Givens κ) :
    List (κ × Nat) → List STy → List Dict → Prop where
  | nil {args : List STy} : EntailsAll impls givens [] args []
  | cons {tr : κ} {j : Nat} {ctx : List (κ × Nat)} {args : List STy} {τ : STy}
      {d : Dict} {ds : List Dict} :
      args[j]? = some τ → Entails impls givens tr τ d → EntailsAll impls givens ctx args ds →
      EntailsAll impls givens ((tr, j) :: ctx) args (d :: ds)

end

/-! ## Finding it -/

/-- The first implementation of `tr` for `head` at this arity, with its place. -/
def findImpl (tr : κ) (head : String) (n : Nat) : List (Impl κ) → Option (Nat × Impl κ)
  | [] => none
  | I :: rest =>
    if I.trait == tr && I.head == head && I.arity == n then some (0, I)
    else (findImpl tr head n rest).map fun x => (x.1 + 1, x.2)

/-- Where an assumption is among those a function makes. -/
def findGiven (tr : κ) (v : Nat) : Givens κ → Option Nat
  | [] => none
  | g :: rest => if g == (tr, v) then some 0 else (findGiven tr v rest).map (· + 1)

/-- Meet each condition of an implementation, given how to meet a bound. -/
def collect (f : κ → STy → Option Dict) (args : List STy) :
    List (κ × Nat) → Option (List Dict)
  | [] => some []
  | (tr, j) :: ctx =>
    match args[j]? with
    | none => none
    | some τ =>
      match f tr τ, collect f args ctx with
      | some d, some ds => some (d :: ds)
      | _, _ => none

/-- How `tr` holds of a type, if it can be found within `fuel` implementations
one inside another, the implementation for a trait, a head and an arity found
by `find`; for a tuple of one or more none is, one for its first and the
rest. A type variable has a trait only if that is assumed. -/
def solveBy (find : κ → String → Nat → Option (Nat × Impl κ)) (givens : Givens κ) :
    Nat → κ → STy → Option Dict
  | 0, _, _ => none
  | _ + 1, tr, .var v => (findGiven tr v givens).map .given
  | fuel + 1, tr, .con head args =>
    match find tr head args.length with
    | some (i, I) => (collect (solveBy find givens fuel) args I.context).map (.impl i)
    | none =>
      match consView head args with
      | none => none
      | some (head', args') =>
        match find tr head' 2 with
        | none => none
        | some (i, I) => (collect (solveBy find givens fuel) args' I.context).map (.impl i)

/-- `solveBy`, the implementations looked for in order. -/
def solve (impls : List (Impl κ)) (givens : Givens κ) : Nat → κ → STy → Option Dict :=
  solveBy (fun tr head n => findImpl tr head n impls) givens

/-! ## Found by key

The implementations as the checker keeps them: in order, with the place of the
first for each trait, head and arity, and whether a head has any of a trait.
What is found by key is checked to be what is at that place, so it is evidence
as `findImpl`'s is. -/

structure ImplIndex (κ : Type) [BEq κ] [Hashable κ] where
  impls : Array (Impl κ) := #[]
  first : Std.HashMap (κ × String × Nat) Nat := {}
  heads : Std.HashMap (κ × String) Nat := {}

/-- One more implementation, after the others. -/
def ImplIndex.push (ix : ImplIndex κ) (I : Impl κ) : ImplIndex κ :=
  let i := ix.impls.size
  { impls := ix.impls.push I
    first := if ix.first.contains (I.trait, I.head, I.arity) then ix.first else ix.first.insert (I.trait, I.head, I.arity) i
    heads := if ix.heads.contains (I.trait, I.head) then ix.heads else ix.heads.insert (I.trait, I.head) i }

/-- The implementations, indexed. -/
def ImplIndex.ofArray (impls : Array (Impl κ)) : ImplIndex κ := impls.foldl ImplIndex.push {}

/-- The first implementation of `tr` for `head` at this arity, with its place. -/
def ImplIndex.find (ix : ImplIndex κ) (tr : κ) (head : String) (n : Nat) : Option (Nat × Impl κ) :=
  match ix.first[(tr, head, n)]? with
  | some i =>
    match ix.impls[i]? with
    | some I => if I.trait == tr && I.head == head && I.arity == n then some (i, I) else none
    | none => none
  | none => none

/-- The first implementation of `tr` for `head`, at any arity. -/
def ImplIndex.firstFor (ix : ImplIndex κ) (tr : κ) (head : String) : Option (Impl κ) :=
  ix.heads[(tr, head)]?.bind (ix.impls[·]?)

/-- Is there an implementation of `tr` for `head`? -/
def ImplIndex.has (ix : ImplIndex κ) (tr : κ) (head : String) : Bool := ix.heads.contains (tr, head)

/-- `solve`, the implementations found by key. -/
def solveIx (ix : ImplIndex κ) (givens : Givens κ) : Nat → κ → STy → Option Dict :=
  solveBy ix.find givens

/-! ## At most one way -/

/-! ## Checking the conditions -/

/-- Is no implementation for the same trait and head as a later one? -/
def noOverlap : List (Impl κ) → Bool
  | [] => true
  | I :: rest =>
    rest.all (fun J => !(I.trait == J.trait && I.head == J.head && I.arity == J.arity))
      && noOverlap rest

/-- An implementation for a tuple of one or more, or a function, that one
for every length (`J`) would be for too? -/
def overlapsView (I J : Impl κ) : Bool :=
  (I.trait == J.trait) && decide (0 < I.arity) &&
    (decide (J.head = consHead) && decide (I.head = tupleHead I.arity)
      || decide (J.head = fnHead) && decide (I.head = fnArityHead (I.arity - 1)))

/-- Has no trait an implementation for a tuple of one or more beside one for
its first and the rest, nor for a function of some number of arguments
beside one for every number? -/
def noConsOverlap (impls : List (Impl κ)) : Bool :=
  impls.all fun J => impls.all fun I => !overlapsView I J

/-- `noOverlap`, as a set of what each implementation is for: the same
answer, in a step for each implementation rather than for each pair of
them, which over the library's and a program's thousands made checking a
module's declarations quadratic. -/
def noOverlapFast (impls : List (Impl κ)) : Bool := Id.run do
  let mut seen : Std.HashSet (κ × String × Nat) := {}
  for I in impls do
    if seen.contains (I.trait, I.head, I.arity) then return false
    seen := seen.insert (I.trait, I.head, I.arity)
  return true

/-- `noConsOverlap`, likewise: the traits with an implementation for every
length of tuple, and for every length of function, found first. -/
def noConsOverlapFast (impls : List (Impl κ)) : Bool :=
  let cons : Std.HashSet κ := impls.foldl (fun s J => if J.head == consHead then s.insert J.trait else s) {}
  let fns : Std.HashSet κ := impls.foldl (fun s J => if J.head == fnHead then s.insert J.trait else s) {}
  impls.all fun I =>
    !(0 < I.arity && (cons.contains I.trait && I.head == tupleHead I.arity
      || fns.contains I.trait && I.head == fnArityHead (I.arity - 1)))

/-- Is nothing assumed twice? -/
def distinct : Givens κ → Bool
  | [] => true
  | g :: rest => !rest.contains g && distinct rest

end Glorious.Traits
