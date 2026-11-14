module

public import Glorious.Elab.Base

/-!
# A function for each implementation it is used at

Once a program's traits are written out (`untrait`), a function that needs a
trait of one of its type parameters takes the implementation as a value, and
a call of one of the trait's functions takes the function out of that value.
Where a call gives an implementation that is known, nothing about it is left
to find out when the program runs: so the function called is written out
again for that implementation, with the trait's functions called by name.

    fn total<W: Get<T>>(world: &W) .. <W as Get<T>>::take(world) ..
    total(&world)        -- `total` for this world: `take` is the function
                         -- of the implementation that fits it, called directly

Everything a program reaches from `main` is then free of implementations as
values: `main` is known none, and each copy is made for ones that are known.
What is left with them is what nothing calls.

The copies keep the numbers of the calls in them, by which the checker's
findings are known. A copy made for a call that gave its implementations as
arguments takes `()` in their places, so that the places of the other
arguments are what the checker counted; one made for a function taken out
of an implementation has no such places, as that call had none.
-/

public section

namespace Glorious.Elab

open Glorious.Syntax

/-- An implementation as a value with nothing left to be known: the function
that makes one, known others like it. -/
partial def closedDict (impls : List ImplE) : Expr → Bool
  | .call _ (.name none f) subs => impls.any (·.dictFn == f) && subs.all (closedDict impls)
  | _ => false

/-- Such a value as it is written into a name. -/
partial def dictKey : Expr → String
  | .call _ (.name none f) [] => f
  | .call _ (.name none f) subs => s!"{f}({", ".intercalate (subs.map dictKey)})"
  | _ => "?"

/-- The copies asked for: each by its name, with the function it is of, the
implementations it is for, and whether their places are dropped. -/
abbrev Copies := List (String × String × List Expr × Bool)

def askCopy (fn : String) (dicts : List Expr) (drop : Bool) : StateM Copies String := do
  let name := s!"{fn}⟨{", ".intercalate (dicts.map dictKey)}⟩{if drop then "'" else ""}"
  unless (← get).any (·.1 == name) do
    modify fun copies => copies ++ [(name, fn, dicts, drop)]
  pure name

mutual

/-- An expression of a function written out for the implementations `known`
(by the names its parameters for them had). -/
partial def specExpr (tr : TraitInfo) (known : List (String × Expr)) : Expr → StateM Copies Expr
  | .name none x => pure ((known.lookup x).getD (.name none x))
  | .call id f args => do
    let (f, args) ← specCall tr known f args
    pure (.call id f args)
  | .tailCall id f args => do
    let (f, args) ← specCall tr known f args
    pure (.tailCall id f args)
  | .tuple args => .tuple <$> args.mapM (specExpr tr known)
  | .proj e n => do pure (.proj (← specExpr tr known e) n)
  | .closure id clauses => .closure id <$> clauses.mapM (specClause tr known)
  | .handle subject arms => do
    pure (.handle (← specExpr tr known subject) (← arms.mapM (specClause tr known)))
  | .labelScope l body => .labelScope l <$> specStmts tr known body
  | .deref e => .deref <$> specExpr tr known e
  | .reborrow uniq e => .reborrow uniq <$> specExpr tr known e
  | .fieldOf id e name => do pure (.fieldOf id (← specExpr tr known e) name)
  | e => pure e

/-- What is called and what it is known, at a call. -/
partial def specCall (tr : TraitInfo) (known : List (String × Expr)) (f : Expr) (args : List Expr) :
    StateM Copies (Expr × List Expr) := do
  let args ← args.mapM (specExpr tr known)
  match f with
  | .proj d idx =>
    -- A trait's function taken out of an implementation that is known: the
    -- implementation's function, for what its own conditions are met by.
    let d ← specExpr tr known d
    match d with
    | .call _ (.name none dictFn) subs =>
      match closedDict tr.impls d, (tr.impls.find? (·.dictFn == dictFn)).bind (·.methods[idx]?) with
      | true, some (fn, _) =>
        if subs.isEmpty then pure (.name none fn, args)
        else pure (.name none (← askCopy fn subs true), args)
      | _, _ => pure (.proj d idx, args)
    | _ => pure (.proj d idx, args)
  | .name none g =>
    let n := (tr.bounded.lookup g).getD 0
    if n > 0 && args.length ≥ n && (args.take n).all (closedDict tr.impls) then
      let copy ← askCopy g (args.take n) false
      pure (.name none copy, List.replicate n (.tuple []) ++ args.drop n)
    else pure (.name none g, args)
  | f => do pure (← specExpr tr known f, args)

partial def specClause (tr : TraitInfo) (known : List (String × Expr)) : Clause → StateM Copies Clause
  | .mk pats body => .mk pats <$> specStmts tr known body

partial def specStmts (tr : TraitInfo) (known : List (String × Expr)) (stmts : List Stmt) :
    StateM Copies (List Stmt) :=
  stmts.mapM (specStmt tr known)

partial def specStmt (tr : TraitInfo) (known : List (String × Expr)) : Stmt → StateM Copies Stmt
  | .let_ pat value => .let_ pat <$> specExpr tr known value
  | .expr e => .expr <$> specExpr tr known e
  | .defer e => .defer <$> specExpr tr known e
  | .letMut x value => .letMut x <$> specExpr tr known value
  | .assign target value => do pure (.assign (← specExpr tr known target) (← specExpr tr known value))
  | .located line col s => .located line col <$> specStmt tr known s

end

/-- A function given no implementation, with the calls in it sent to copies. -/
def specRoot (tr : TraitInfo) (item : Item) : StateM Copies Item :=
  match item with
  | .fn name ps annots ret clauses =>
    if (tr.bounded.lookup name).getD 0 == 0 then do
      let clauses ← clauses.mapM (specClause tr [])
      pure (Item.fn name ps annots ret clauses)
    else pure item
  | other => pure other

mutual

/-- Does an expression name the label `l`? -/
partial def namesLabel (l : String) : Expr → Bool
  | .label x => x == l
  | .call _ f args => namesLabel l f || args.any (namesLabel l)
  | .tailCall _ f args => namesLabel l f || args.any (namesLabel l)
  | .tuple args => args.any (namesLabel l)
  | .proj e _ => namesLabel l e
  | .closure _ clauses => clauses.any fun
    | .mk _ body => body.any (stmtNamesLabel l)
  | .handle subject arms => namesLabel l subject || arms.any fun
    | .mk _ body => body.any (stmtNamesLabel l)
  | .labelScope x body => x != l && body.any (stmtNamesLabel l)
  | .deref e => namesLabel l e
  | .reborrow _ e => namesLabel l e
  | .fieldOf _ e _ => namesLabel l e
  | _ => false

partial def stmtNamesLabel (l : String) : Stmt → Bool
  | .let_ _ value => namesLabel l value
  | .expr e => namesLabel l e
  | .defer e => namesLabel l e
  | .letMut _ value => namesLabel l value
  | .assign target value => namesLabel l target || namesLabel l value
  | .located _ _ s => stmtNamesLabel l s

end

/-- A clause of a copy: the parameters for implementations dropped, or each
taking `()`, and the body written out for the implementations. -/
def specCopyClause (tr : TraitInfo) (known : List (String × Expr)) (n : Nat) (drop : Bool)
    (fn : String) (clause : Clause) : StateM Copies Clause :=
  match clause with
  | .mk pats body => do
    let pats := if drop then pats.drop n else List.replicate n Pattern.wild ++ pats.drop n
    let body ← specStmts tr known body
    -- (A function's name is the label its body leaves by, `@find(..)`: the
    -- copy has another name, so its body is given that label.)
    let body := if body.any (stmtNamesLabel fn) then [Stmt.expr (.labelScope fn body)] else body
    pure (Clause.mk pats body)

/-- A program with a copy of each function for each known implementation it
is called with, and the names of the copies with the functions they are of.
`fuel` bounds how many are made: a program that would need more (a function
that calls itself with an implementation made from the one it was given) is
left as it was. -/
partial def specialize (tr : TraitInfo) (items : List Item) (fuel : Nat := 50000) :
    List Item × List (String × String) :=
  let fns : List (String × Item) := items.filterMap fun (item : Item) =>
    match item with
    | .fn name _ _ _ _ => some (name, item)
    | _ => none
  let (roots, asked) := (items.mapM (specRoot tr)).run []
  let rec make (fuel done : Nat) (copies : Copies) (out : Array Item) : Option (Array Item × Copies) :=
    match fuel, copies[done]? with
    | _, none => some (out, copies)
    | 0, some _ => none
    | fuel + 1, some (name, fn, dicts, drop) =>
      match fns.lookup fn with
      | some (.fn _ ps annots ret clauses) =>
        let n := dicts.length
        let known : List (String × Expr) :=
          (List.range n).map fun k => (s!"%dict{k}", dicts[k]?.getD (Expr.tuple []))
        let (clauses, copies) := (clauses.mapM (specCopyClause tr known n drop fn)).run copies
        let annots := if drop then annots.drop n else annots
        make fuel (done + 1) copies (out.push (Item.fn name ps annots ret clauses))
      | _ => make fuel (done + 1) copies out
  match make fuel 0 asked #[] with
  | some (made, copies) => (roots ++ made.toList, copies.map fun (name, fn, _, _) => (name, fn))
  | none => (items, [])

/-! ## `..` in a tuple pattern

How many parts the `..` of `(first, ..)` stands for is known once the
tuple's type is. The checker says so, and the program is then read with that
many `_` written in its place. -/

mutual

partial def restPat (id count : Nat) : Pattern → Pattern
  | .tuple ps => .tuple (ps.flatMap fun
      | .var x => if Syntax.tupleRestOf x == some id then List.replicate count Pattern.wild else [.var x]
      | p => [restPat id count p])
  | .ctor c q ps => .ctor c q (ps.map (restPat id count))
  | p => p

partial def restExprIn (id count : Nat) : Expr → Expr
  | .call i f args => .call i (restExprIn id count f) (args.map (restExprIn id count))
  | .tailCall i f args => .tailCall i (restExprIn id count f) (args.map (restExprIn id count))
  | .tuple args => .tuple (args.map (restExprIn id count))
  | .proj e n => .proj (restExprIn id count e) n
  | .closure i clauses => .closure i (clauses.map (restClause id count))
  | .handle subject arms => .handle (restExprIn id count subject) (arms.map (restClause id count))
  | .labelScope l body => .labelScope l (body.map (restStmt id count))
  | .deref e => .deref (restExprIn id count e)
  | .reborrow uniq e => .reborrow uniq (restExprIn id count e)
  | .fieldOf i e name => .fieldOf i (restExprIn id count e) name
  | e => e

partial def restClause (id count : Nat) : Clause → Clause
  | .mk pats body => .mk (pats.map (restPat id count)) (body.map (restStmt id count))

partial def restStmt (id count : Nat) : Stmt → Stmt
  | .let_ pat value => .let_ (restPat id count pat) (restExprIn id count value)
  | .expr e => .expr (restExprIn id count e)
  | .defer e => .defer (restExprIn id count e)
  | .letMut x value => .letMut x (restExprIn id count value)
  | .assign target value => .assign (restExprIn id count target) (restExprIn id count value)
  | .located line col s => .located line col (restStmt id count s)

end

/-- A program with the `..` of one tuple pattern written as so many `_`. -/
partial def restItems (id count : Nat) (items : List Item) : List Item :=
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map (restClause id count))
    | .impl ps tr head args context methods => .impl ps tr head args context (restItems id count methods)
    | .traitInfo n supers defaults params assocs => .traitInfo n supers (restItems id count defaults) params assocs
    | .module name (some body) => .module name (some (restItems id count body))
    | .pub parent item => .pub parent ((restItems id count [item]).headD item)
    | item => item

/-- What the checker said of a tuple pattern's `..`, if that is what it said:
which pattern, and how many parts. -/
def restFound (said : String) : Option (Nat × Nat) :=
  match said.splitOn "%tuplerest:" with
  | _ :: after :: _ =>
    match ((after.splitOn "%").headD "").splitOn ":" with
    | [id, count] => id.toNat?.bind fun id => count.toNat?.map fun count => (id, count)
    | _ => none
  | _ => none

end Glorious.Elab
