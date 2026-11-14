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

/-! ## Constants worked out once

After the copies are made, a trait's constant at a known type is a call of a
function that takes nothing: `<B1<B0<Z>> as Known>::VALUE` is a function
that adds one to twice another. Such a function whose body is integer
arithmetic of numbers and of such calls has its number worked out here, and
every call of it is that number. A result that does not fit in 64 bits is
left to go wrong when the program runs, as it would have. -/

/-- A function's one clause, if its body is one expression. -/
def oneExpr : List Clause → Option (List Pattern × Expr)
  | [.mk pats [.expr body]] => some (pats, body)
  | [.mk pats [.located _ _ (.expr body)]] => some (pats, body)
  | _ => none

/-- The number an expression stands for, given the numbers of the names in
`env` and the functions `fns`, if it is one: numbers, `int_add`, `int_sub`
and `int_mul` of numbers, and calls of functions whose one clause takes plain
names and is one expression. `fuel` bounds the calls followed. -/
partial def foldInt (fns : List (String × List Clause)) (env : List (String × Int)) (fuel : Nat) :
    Expr → Option Int
  | .int n => some n
  | .name none x => env.lookup x
  | .call _ (.name none f) args => do
    if fuel == 0 then none
    -- (A type written for a value, or for a function's parameters, says
    -- nothing of its number.)
    if f == Syntax.ascribeMark || f == Syntax.instMark then
      match args with
      | a :: _ => foldInt fns env (fuel - 1) a
      | [] => none
    else
      let vals ← args.mapM (foldInt fns env (fuel - 1))
      let fits := fun (n : Int) =>
        if -9223372036854775808 ≤ n && n ≤ 9223372036854775807 then some n else none
      match f, vals with
      | "int_add", [a, b] => fits (a + b)
      | "int_sub", [a, b] => fits (a - b)
      | "int_mul", [a, b] => fits (a * b)
      | _, _ =>
        match (fns.lookup f).bind oneExpr with
        | some (pats, body) =>
          let names ← pats.mapM fun
            | .var x => some x
            | _ => none
          if names.length != vals.length then none
          else foldInt fns (names.zip vals) (fuel - 1) body
        | none => none
  | _ => none

mutual

partial def foldExpr (known : List (String × Int)) : Expr → Expr
  | .call id (.name none f) [] => match known.lookup f with
    | some n => .int n
    | none => .call id (.name none f) []
  | .call id (.name none mark) (.call i (.name none f) [] :: rest) =>
    match known.lookup f with
    | some n => if mark == Syntax.instMark then .int n else .call id (.name none mark) (.int n :: rest)
    | none => .call id (.name none mark) (.call i (.name none f) [] :: rest.map (foldExpr known))
  | .call id f args => .call id (foldExpr known f) (args.map (foldExpr known))
  | .tailCall id f args => .tailCall id (foldExpr known f) (args.map (foldExpr known))
  | .tuple args => .tuple (args.map (foldExpr known))
  | .proj e n => .proj (foldExpr known e) n
  | .closure id clauses => .closure id (clauses.map (foldClause known))
  | .handle subject arms => .handle (foldExpr known subject) (arms.map (foldClause known))
  | .labelScope l body => .labelScope l (body.map (foldStmt known))
  | .deref e => .deref (foldExpr known e)
  | .reborrow uniq e => .reborrow uniq (foldExpr known e)
  | .fieldOf i e name => .fieldOf i (foldExpr known e) name
  | e => e

partial def foldClause (known : List (String × Int)) : Clause → Clause
  | .mk pats body => .mk pats (body.map (foldStmt known))

partial def foldStmt (known : List (String × Int)) : Stmt → Stmt
  | .let_ pat value => .let_ pat (foldExpr known value)
  | .expr e => .expr (foldExpr known e)
  | .defer e => .defer (foldExpr known e)
  | .letMut x value => .letMut x (foldExpr known value)
  | .assign target value => .assign (foldExpr known target) (foldExpr known value)
  | .located line col s => .located line col (foldStmt known s)

end

/-- A program with every call of a function that takes nothing and works out
to a number written as that number. -/
def foldConstants (items : List Item) : List Item :=
  let fns : List (String × List Clause) := items.filterMap fun
    | .fn name _ _ _ clauses => some (name, clauses)
    | _ => none
  let known : List (String × Int) := fns.filterMap fun (name, clauses) =>
    match oneExpr clauses with
    | some ([], body) => (foldInt fns [] 64 body).map (name, ·)
    | _ => none
  if known.isEmpty then items
  else items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map (foldClause known))
    | item => item

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

/-! ## A value used on one path and not on another

A value with a `drop` to run that one path uses and another does not is kept
in a variable, as `let mut` keeps it: where it was not used, the variable
destroys it. The checker says which `let`, and the program is read again with
that `let` written as `let mut`. -/

/-- The `let` the checker asks to keep its value in a variable, if it does:
the function, its place and the name. -/
def letMutFound (said : String) : Option (String × Nat × Nat × String) :=
  match said.splitOn "%letmut:" with
  | _ :: after :: _ =>
    match ((after.splitOn "%").headD "").splitOn ":" with
    | line :: col :: x :: owner =>
      line.toNat?.bind fun line => col.toNat?.map fun col => (":".intercalate owner, line, col, x)
    | _ => none
  | _ => none

/-- What the checker says, without the marker. -/
def withoutLetMut (said : String) : String :=
  match said.splitOn "%letmut:" with
  | before :: after :: _ => before ++ (((after.splitOn "%").drop 1).foldl (· ++ ·) "")
  | _ => said

mutual

partial def letMutExpr (line col : Nat) (x : String) : Expr → Expr
  | .call i f args => .call i (letMutExpr line col x f) (args.map (letMutExpr line col x))
  | .tailCall i f args => .tailCall i (letMutExpr line col x f) (args.map (letMutExpr line col x))
  | .tuple args => .tuple (args.map (letMutExpr line col x))
  | .proj e n => .proj (letMutExpr line col x e) n
  | .closure i clauses => .closure i (clauses.map (letMutClause line col x))
  | .handle subject arms => .handle (letMutExpr line col x subject) (arms.map (letMutClause line col x))
  | .labelScope l body => .labelScope l (body.map (letMutStmt line col x))
  | .deref e => .deref (letMutExpr line col x e)
  | .reborrow uniq e => .reborrow uniq (letMutExpr line col x e)
  | .fieldOf i e name => .fieldOf i (letMutExpr line col x e) name
  | e => e

partial def letMutClause (line col : Nat) (x : String) : Clause → Clause
  | .mk pats body => .mk pats (body.map (letMutStmt line col x))

partial def letMutStmt (line col : Nat) (x : String) : Stmt → Stmt
  | .located l c (.let_ (.var y) value) =>
    if l == line && c == col && y == x then .located l c (.letMut y (letMutExpr line col x value))
    else .located l c (.let_ (.var y) (letMutExpr line col x value))
  | .let_ pat value => .let_ pat (letMutExpr line col x value)
  | .expr e => .expr (letMutExpr line col x e)
  | .defer e => .defer (letMutExpr line col x e)
  | .letMut y value => .letMut y (letMutExpr line col x value)
  | .assign target value => .assign (letMutExpr line col x target) (letMutExpr line col x value)
  | .located l c s => .located l c (letMutStmt line col x s)

end

/-- A program with one function's `let x` at a place written `let mut x`, and
whether there was such a `let`. -/
def letMutItems (owner : String) (line col : Nat) (x : String) (items : List Item) :
    List Item × Bool :=
  let fn := fun (clauses : List Clause) =>
    let after := clauses.map (letMutClause line col x)
    (after, hash after != hash clauses)
  let out : List (Item × Bool) := items.map fun
    | .fn name ps annots ret clauses =>
      if name == owner then
        let (after, changed) := fn clauses
        (Item.fn name ps annots ret after, changed)
      else (Item.fn name ps annots ret clauses, false)
    | .impl ps tr head args context methods =>
      let methods : List (Item × Bool) := methods.map fun
        | .fn m mps annots ret clauses =>
          if implFnName tr head m == owner then
            let (after, changed) := fn clauses
            (Item.fn m mps annots ret after, changed)
          else (Item.fn m mps annots ret clauses, false)
        | item => (item, false)
      (.impl ps tr head args context (methods.map (·.1)), methods.any (·.2))
    | item => (item, false)
  (out.map (·.1), out.any (·.2))

end Glorious.Elab
