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
partial def closedDict (impls : Std.HashMap String ImplE) : Expr → Bool
  | .call _ (.name none f) subs => impls.contains f && subs.all (closedDict impls)
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
  | e => e.traverse (specExpr tr known) fun _ b => specStmts tr known b

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
      match closedDict tr.implsAt d, (tr.implsAt[dictFn]?).bind (·.methods[idx]?) with
      | true, some (fn, _) =>
        if subs.isEmpty then pure (.name none fn, args)
        else pure (.name none (← askCopy fn subs true), args)
      | _, _ => pure (.proj d idx, args)
    | _ => pure (.proj d idx, args)
  | .name none g =>
    let n := (tr.boundedAt[g]?).getD 0
    if n > 0 && args.length ≥ n && (args.take n).all (closedDict tr.implsAt) then
      let copy ← askCopy g (args.take n) false
      pure (.name none copy, List.replicate n (.tuple []) ++ args.drop n)
    else pure (.name none g, args)
  | f => do pure (← specExpr tr known f, args)

partial def specClause (tr : TraitInfo) (known : List (String × Expr)) : Clause → StateM Copies Clause
  | .mk pats body => .mk pats <$> specStmts tr known body

partial def specStmts (tr : TraitInfo) (known : List (String × Expr)) (stmts : List Stmt) :
    StateM Copies (List Stmt) :=
  stmts.mapM (specStmt tr known)

partial def specStmt (tr : TraitInfo) (known : List (String × Expr)) (s : Stmt) : StateM Copies Stmt :=
  s.traverse (specExpr tr known)

end

/-- A function given no implementation, with the calls in it sent to copies. -/
def specRoot (tr : TraitInfo) (item : Item) : StateM Copies Item :=
  match item with
  | .fn name ps annots ret clauses =>
    if (tr.boundedAt[name]?).getD 0 == 0 then do
      let clauses ← clauses.mapM (specClause tr [])
      pure (Item.fn name ps annots ret clauses)
    else pure item
  | other => pure other

/-- Does an expression name the label `l`? -/
partial def namesLabel (l : String) : Expr → Bool
  | .label x => x == l
  | .labelScope x body => x != l && body.any (·.exprs.any (namesLabel l))
  | e => e.children.any (namesLabel l)

def stmtNamesLabel (l : String) (s : Stmt) : Bool := s.exprs.any (namesLabel l)

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

/-- Each call of a function that takes nothing and works out to a number
(`known`) written as that number. -/
def foldRewrite (known : List (String × Int)) : Rewrite where
  onExpr go
    | .call _ (.name none f) [] => (known.lookup f).map .int
    | .call id (.name none mark) (.call i (.name none f) [] :: rest) =>
      some (match known.lookup f with
        | some n => if mark == Syntax.instMark then .int n else .call id (.name none mark) (.int n :: rest)
        | none => .call id (.name none mark) (.call i (.name none f) [] :: rest.map go.ex))
    | _ => none

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
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map (foldRewrite known).clause)
    | item => item

/-! ## `..` in a tuple pattern

How many parts the `..` of `(first, ..)` stands for is known once the
tuple's type is. The checker says so, and the program is then read with that
many `_` written in its place. -/

partial def restPat (id count : Nat) : Pattern → Pattern
  | .tuple ps => .tuple (ps.flatMap fun
      | .var x => if Syntax.tupleRestOf x == some id then List.replicate count Pattern.wild else [.var x]
      | p => [restPat id count p])
  | .ctor c q ps => .ctor c q (ps.map (restPat id count))
  | p => p

/-- A program with the `..` of one tuple pattern written as so many `_`. -/
def restItems (id count : Nat) : List Item → List Item :=
  Rewrite.items { onPat := restPat id count }

/-- What the checker said of a tuple pattern's `..`, if that is what it said:
which pattern, and how many parts. -/
def restFound (said : String) : Option (Nat × Nat) :=
  match said.splitOn "%tuplerest:" with
  | _ :: after :: _ =>
    match ((after.splitOn "%").headD "").splitOn ":" with
    | [id, count] => id.toNat?.bind fun id => count.toNat?.map fun count => (id, count)
    | _ => none
  | _ => none

/-! ## Patterns of a value matched against a reference

`match(s) { Dot => 0, Line(n) => *n }` for `s: &Shape`: the checker says which
callable's clauses, and the program is read again with their first patterns
written `&Dot`, `&Line(n)`, so that they look at what the reference points to
and bind references, as Rust's binding modes have it. -/

/-- A program with the first patterns of one callable's clauses written
`&Pattern`. -/
def refPatsItems (id : Nat) (uniq : Bool) (which : List Nat) : List Item → List Item :=
  -- (The callable is one: nothing inside it is changed.)
  Rewrite.items { onExpr := fun _ => fun
    | .closure i clauses =>
      if i != id then none else
      some (.closure i (clauses.zipIdx.map fun (c, k) => match c with
        | .mk (p :: ps) body =>
          if which.contains k then .mk (.ctor (Syntax.byRefMark uniq) none [p] :: ps) body else c
        | c => c))
    | _ => none }

/-- What the checker said of such clauses, if that is what it said. -/
def refPatsFound (said : String) : Option (Nat × Bool × List Nat) :=
  match said.splitOn "%refpats:" with
  | _ :: after :: _ =>
    match ((after.splitOn "%").headD "").splitOn ":" with
    | [id, u, ks] => id.toNat?.map fun id => (id, u == "1", (ks.splitOn ",").filterMap String.toNat?)
    | _ => none
  | _ => none

/-- What the checker says, without that mark. -/
def withoutRefPats (said : String) : String :=
  match said.splitOn "%refpats:" with
  | before :: after :: _ => before ++ "%".intercalate ((after.splitOn "%").drop 1)
  | _ => said

/-! ## A dot call of a type's own function

`v.push(x)` where `push` is a function in scope that does not fit `v`, and
`v`'s type has a `push` of its own: the checker says so, and the program is
read again with the call written as one of that function
(`.fieldOf _ v "%own:std::vec::Vec::push"`, which the resolver reads). -/

def dotOwnItems (call : Nat) (fn : String) : List Item → List Item :=
  Rewrite.items { onExpr := fun go => fun
    | .call i (.fieldOf fi recv _) args =>
      if i == call then some (.call i (.fieldOf fi (go.ex recv) ("%own:" ++ fn)) (args.map go.ex)) else none
    | _ => none }

/-- A program with the receiver of one dot call, a name, borrowed:
`Syntax.recvRefMark`. -/
def recvRefItems (call : Nat) (uniq : Bool) : List Item → List Item :=
  Rewrite.items { onExpr := fun go => fun
    | .call i (.fieldOf fi (.name none x) name) args =>
      if i == call then some (.call i (.fieldOf fi (.ref uniq x) name) (args.map go.ex)) else none
    | _ => none }

def recvRefFound (said : String) : Option (Nat × Bool) :=
  match said.splitOn "%recvref:" with
  | _ :: after :: _ =>
    match ((after.splitOn "%").headD "").splitOn ":" with
    | [call, u] => call.toNat?.map fun c => (c, u == "1")
    | _ => none
  | _ => none

def withoutRecvRef (said : String) : String :=
  match said.splitOn "%recvref:" with
  | before :: after :: _ => before ++ "%".intercalate ((after.splitOn "%").drop 1)
  | _ => said

def dotOwnFound (said : String) : Option (Nat × String) :=
  match said.splitOn "%dotown:" with
  | _ :: after :: _ =>
    match ((after.splitOn "%").headD "").splitOn ":" with
    | call :: fn => call.toNat?.map fun c => (c, ":".intercalate fn)
    | _ => none
  | _ => none

def withoutDotOwn (said : String) : String :=
  match said.splitOn "%dotown:" with
  | before :: after :: _ => before ++ "%".intercalate ((after.splitOn "%").drop 1)
  | _ => said

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

/-- A program with the clauses of one function, of the program or of an
implementation, made by `f`; and whether they changed. -/
def ownerItems (owner : String) (f : List Clause → List Clause) (items : List Item) :
    List Item × Bool :=
  let fn := fun (clauses : List Clause) =>
    let after := f clauses
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

/-- The `let x` at `line:col` written `let mut x`; a name a pattern binds kept
in a variable straight after. At place `0:0`, a clause that takes `x` as a
parameter (or a name its patterns bind) starts by keeping it in a variable,
written at the place of its first statement. -/
def letMutRewrite (line col : Nat) (x : String) : Rewrite where
  onStmts go
    | .located l c (.let_ pat value) :: rest =>
      if l != line || c != col then none else
      let value := go.ex value
      let rest := go.stmts rest
      some (match pat with
        | .var y =>
          if y == x then .located l c (.letMut y value) :: rest
          else .located l c (.let_ pat value) :: rest
        | _ =>
          if (patVars pat).contains x then
            .located l c (.let_ pat value) :: .located l c (.letMut x (.name none x)) :: rest
          else .located l c (.let_ pat value) :: rest)
    | _ => none
  onClause go
    | .mk pats body =>
      if line != 0 || col != 0 || !(pats.flatMap patVars).contains x then none else
      some (match go.stmts body with
        | .located l c s :: rest => .mk pats (.located l c (.letMut x (.name none x)) :: .located l c s :: rest)
        | body => .mk pats body)

/-- A program with one function's `let x` at a place written `let mut x`, and
whether there was such a `let`. -/
def letMutItems (owner : String) (line col : Nat) (x : String) (items : List Item) :
    List Item × Bool :=
  ownerItems owner (·.map (letMutRewrite line col x).clause) items

/-- What `etaMark` said: the function it is in, the function named, and how
many parameters. -/
def etaFound (said : String) : Option (String × String × Nat) :=
  match said.splitOn "%eta:" with
  | _ :: after :: _ =>
    match ((after.splitOn "%").headD "").splitOn ":" with
    | arity :: x :: owner => arity.toNat?.map fun n => (":".intercalate owner, x, n)
    | _ => none
  | _ => none

/-- What the checker says, without the marker. -/
def withoutEta (said : String) : String :=
  match said.splitOn "%eta:" with
  | before :: after :: _ => before ++ (((after.splitOn "%").drop 1).foldl (· ++ ·) "")
  | _ => said

mutual

/-- An expression with each naming of `x` that is not a call of it a block
that calls it: `{ (a, b) => x(a, b) }`. -/
partial def etaExpr (x : String) (arity : Nat) (base : Nat) : Expr → Expr
  | .name q y =>
    if y == x then
      let ps := (List.range arity).map fun i => s!"%eta{i}"
      .closure base [.mk (ps.map Pattern.var) [.expr (.call (base + 1) (.name q y) (ps.map (Expr.name none ·)))]]
    else .name q y
  | .call i (.name q y) args => .call i (.name q y) (args.map (etaExpr x arity (base + 2 * (i % 1000000))))
  | .call i f args => .call i (etaExpr x arity base f) (args.map (etaExpr x arity (base + 2 * (i % 1000000))))
  | .tailCall i f args => .tailCall i (match f with
      | .name q y => .name q y
      | f => etaExpr x arity base f) (args.map (etaExpr x arity (base + 2 * (i % 1000000))))
  | .tuple args => .tuple (args.zipIdx.map fun (e, k) => etaExpr x arity (base + 2 * k + 1000000000) e)
  | .proj e n => .proj (etaExpr x arity base e) n
  | .closure i clauses => .closure i (clauses.map (etaClause x arity base))
  | .handle subject arms => .handle (etaExpr x arity base subject) (arms.map (etaClause x arity base))
  | .labelScope l body => .labelScope l (body.map (etaStmt x arity base))
  | .deref e => .deref (etaExpr x arity base e)
  | .reborrow uniq e => .reborrow uniq (etaExpr x arity base e)
  | .fieldOf i e name => .fieldOf i (etaExpr x arity base e) name
  | e => e

partial def etaClause (x : String) (arity : Nat) (base : Nat) : Clause → Clause
  | .mk pats body => .mk pats (body.map (etaStmt x arity base))

partial def etaStmt (x : String) (arity : Nat) (base : Nat) : Stmt → Stmt
  | .let_ pat value => .let_ pat (etaExpr x arity base value)
  | .expr e => .expr (etaExpr x arity base e)
  | .defer e => .defer (etaExpr x arity base e)
  | .letMut y value => .letMut y (etaExpr x arity base value)
  | .assign target value => .assign (etaExpr x arity base target) (etaExpr x arity base value)
  | .located l c s => .located l c (etaStmt x arity (base + 4000000 * l + 2000 * c) s)

end

/-- A program with each naming of `x` in `owner` that is not a call of it a
block that calls it, and whether there was such a naming. -/
def etaItems (owner x : String) (arity : Nat) (items : List Item) : List Item × Bool :=
  let base := 700000000000000 + 10000000000000 * (hash owner % 16).toNat
  ownerItems owner (·.map (etaClause x arity base)) items

/-! ## A variable whose fields are borrowed apart

`let mut x = (a, b)`, or `let mut c = C { n: a, m: b }` of a struct without
`Drop`, whose fields are borrowed one by one (`&mut x.0`, `&mut c.n`) and that
is otherwise only read, written or read and written by field, is kept as one
variable per field (`x.0`, `c.n`). Then two of its fields can be lent at once,
each a cell of its own, which is what Core's rules for borrows can show (a lend
of a cell takes the whole cell). Reading the variable reads every field;
assigning it assigns each. -/

/-- What a variable that is split holds: its fields' names in order, and how a
whole value is made from them and taken apart into them. -/
structure Split where
  fields : List String
  make : List Expr → Expr
  apart : List Pattern → Pattern

/-- The variable for field `f` of `x`. -/
def fieldVar (x : String) (f : String) : String := s!"{x}.{f}"

/-- Which field a step names: by its name, or by its number. -/
def Split.index (sp : Split) (s : String) : Option Nat :=
  match sp.fields.idxOf? s with
  | some i => some i
  | none => s.toNat?.bind fun i => if i < sp.fields.length then some i else none

def Split.var (sp : Split) (x : String) (i : Nat) : String :=
  fieldVar x ((sp.fields[i]?).getD (toString i))

/-- What follows the making of `x`, with its fields as variables of their
own, up to where a name `x` is made again. -/
def splitRewrite (x : String) (sp : Split) : Rewrite where
  onExpr _
    | .proj (.name none y) i =>
      if y == x && i < sp.fields.length then some (.name none (sp.var x i)) else none
    | .fieldOf _ (.name none y) s =>
      match sp.index s, y == x with
      | some i, true => some (.name none (sp.var x i))
      | _, _ => none
    | .refField id uniq y (s :: path) star =>
      match sp.index s, y == x && !star with
      | some i, true =>
        some (if path.isEmpty then .ref uniq (sp.var x i) else .refField id uniq (sp.var x i) path false)
      | _, _ => none
    | .name none y =>
      if y == x then some (sp.make ((List.range sp.fields.length).map fun i => .name none (sp.var x i)))
      else none
    | _ => none
  onClause _
    | .mk pats body => if (pats.flatMap patVars).contains x then some (.mk pats body) else none
  onStmts go
    | .located l c s :: rest =>
      some (match go.stmts (s :: rest) with
        | first :: more => .located l c first :: more
        | [] => [])
    | .let_ pat value :: rest =>
      if (patVars pat).contains x then some (.let_ pat (go.ex value) :: rest) else none
    | .letMut y value :: rest =>
      if y == x then some (.letMut y (go.ex value) :: rest) else none
    | .assign (.name none y) value :: rest =>
      if y != x then none else
      -- (Assigning the whole: its parts, each to its variable.)
      let parts := (List.range sp.fields.length).map fun i => s!"%{sp.var x i}"
      some (.let_ (sp.apart (parts.map Pattern.var)) (go.ex value)
        :: (parts.zipIdx.map fun (p, i) => Stmt.assign (.name none (sp.var x i)) (.name none p))
        ++ go.stmts rest)
    | _ => none

/-- The statements after `x` is made, with its fields as variables of their
own (`splitRewrite`). -/
def splitStmts (x : String) (sp : Split) : List Stmt → List Stmt := (splitRewrite x sp).stmts

/-- Does `x` have a field borrowed in these statements, before it is made again? -/
partial def fieldBorrowed (x : String) (stmts : List Stmt) : Bool :=
  let rec inExpr : Expr → Bool
    | .refField _ _ y (_ :: _) false => y == x
    | .call _ f args => inExpr f || args.any inExpr
    | .tailCall _ f args => inExpr f || args.any inExpr
    | .tuple args => args.any inExpr
    | .proj e _ => inExpr e
    | .closure _ clauses => clauses.any fun
      | .mk pats body => !(pats.flatMap patVars).contains x && fieldBorrowed x body
    | .handle subject arms => inExpr subject || arms.any fun
      | .mk pats body => !(pats.flatMap patVars).contains x && fieldBorrowed x body
    | .labelScope _ body => fieldBorrowed x body
    | .deref e => inExpr e
    | .reborrow _ e => inExpr e
    | .fieldOf _ e _ => inExpr e
    | _ => false
  match stmts with
  | [] => false
  | .located _ _ s :: rest => fieldBorrowed x (s :: rest)
  | .let_ pat value :: rest => inExpr value || (!(patVars pat).contains x && fieldBorrowed x rest)
  | .letMut y value :: rest => inExpr value || (y != x && fieldBorrowed x rest)
  | .assign target value :: rest => inExpr target || inExpr value || fieldBorrowed x rest
  | .expr e :: rest => inExpr e || fieldBorrowed x rest
  | .defer e :: rest => inExpr e || fieldBorrowed x rest

/-- The structs whose variables can be split: each constructor with its
fields' names, for those without `Drop` (whose value is taken apart only by
its own `drop`). -/
abbrev Structs := List (String × List String)

/-- How a variable made by this value would be split, if it can be. -/
def splitOf (structs : Structs) : Expr → Option (Split × List Expr)
  | .tuple es =>
    if es.length ≥ 2 then
      some (⟨(List.range es.length).map toString, .tuple, .tuple⟩, es)
    else none
  | .call _ (.name q s) args =>
    match structs.lookup s with
    | some names =>
      if names.length ≥ 2 && names.length == args.length then
        some (⟨names, fun vs => .call 0 (.name q s) vs, fun ps => .ctor s q ps⟩, args)
      else none
    | none => none
  | _ => none

/-- Every variable whose fields are borrowed, and that is used no other way
than its fields and its whole value are, made one variable per field. -/
def splitFieldsRewrite (structs : Structs) : Rewrite where
  onStmts go
    | .located l c (.letMut x value) :: rest =>
      (splitOf structs value).bind fun (sp, es) =>
        let split := splitStmts x sp rest
        -- (Kept as it is where it is used some other way: borrowed whole, say.)
        if fieldBorrowed x rest && !(fvStmts [] split).contains x then
          some ((es.zipIdx.map fun (e, i) => Stmt.located l c (.letMut (sp.var x i) (go.ex e)))
            ++ go.stmts split)
        else none
    | _ => none

/-- A program's items with its variables whose fields are borrowed apart made
one variable per field (`splitFieldVars`); `all` are every item of the
program, for the structs and what has `Drop`. -/
def splitFieldItems (all items : List Item) : List Item :=
  let unwrap := fun (item : Item) => match item with
    | .pub _ inner => inner
    | other => other
  let dropped := all.filterMap fun item => match unwrap item with
    | .impl _ tr head _ _ _ => if tr == "Drop" then some head else none
    | _ => none
  let structs : Structs := all.filterMap fun item => match unwrap item with
    | .fieldNames ctor names _ => if dropped.contains ctor then none else some (ctor, names)
    | _ => none
  let clause := (splitFieldsRewrite structs).clause
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map clause)
    | .impl ps tr head args context methods => .impl ps tr head args context (methods.map fun
        | .fn m mps annots ret clauses => .fn m mps annots ret (clauses.map clause)
        | item => item)
    | item => item

/-- A program with what the checker decided written in, in the order it
decided it; and whether each changed something. -/
def decidedItems (decided : List Decision) (items : List Item) : List Item :=
  decided.foldl (fun items d => match d with
    | .rest id count => restItems id count items
    | .eta owner x arity => (etaItems owner x arity items).1
    | .letMut owner line col x => (letMutItems owner line col x items).1) items

/-- What the checker says, if it is something to decide where it was found:
`..` in a tuple pattern, a function named as a value, a value kept in a
variable. -/
def decisionFound (said : String) : Option Decision :=
  match restFound said, etaFound said, letMutFound said with
  | some (id, count), _, _ => some (.rest id count)
  | none, some (owner, x, arity), _ => some (.eta owner x arity)
  | none, none, some (owner, line, col, x) => some (.letMut owner line col x)
  | none, none, none => none

/-- A program with what the checker decided of it written in: `Decision`s
first, then the function of each dot call it chose by the value's type,
with the receiver, a variable, given as that one takes it (`0` as it was,
`1` borrowed, `2` borrowed `&mut`), and each argument it chose to give as
other than written. -/
def decidedProgram (b : Blocks) (items : List Item) : List Item :=
  let items := decidedItems b.decided items
  if b.dotChosen.isEmpty && b.argsChosen.isEmpty then items else
  Rewrite.items (items := items) { onExpr := fun go => fun
    | .call i f args =>
      let args := args.map go.ex
      let (f, args) : Expr × List Expr := match f, b.dotChosen[i]? with
        | .name _ _, some (fn, how) =>
          (.name none fn, match how, args with
            | 0, _ => args
            | k, .name none v :: rest => .ref (k == 2) v :: rest
            | _, _ => args)
        | f, _ => (go.ex f, args)
      some (.call i f (args.zipIdx.map fun (a, k) => b.argsChosen.getD (i, k) a))
    | _ => none }


end Glorious.Elab
