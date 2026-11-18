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

/-! ## Patterns of a value matched against a reference

`match(s) { Dot => 0, Line(n) => *n }` for `s: &Shape`: the checker says which
callable's clauses, and the program is read again with their first patterns
written `&Dot`, `&Line(n)`, so that they look at what the reference points to
and bind references, as Rust's binding modes have it. -/

mutual

partial def refPatsExpr (id : Nat) (uniq : Bool) (which : List Nat) : Expr → Expr
  | .call i f args => .call i (refPatsExpr id uniq which f) (args.map (refPatsExpr id uniq which))
  | .tailCall i f args => .tailCall i (refPatsExpr id uniq which f) (args.map (refPatsExpr id uniq which))
  | .tuple args => .tuple (args.map (refPatsExpr id uniq which))
  | .proj e n => .proj (refPatsExpr id uniq which e) n
  | .closure i clauses =>
    let clauses := clauses.map (refPatsClause id uniq which)
    if i != id then .closure i clauses else
    .closure i (clauses.zipIdx.map fun
      | (.mk (p :: ps) body, k) =>
        if which.contains k then .mk (.ctor (Syntax.byRefMark uniq) none [p] :: ps) body
        else .mk (p :: ps) body
      | (c, _) => c)
  | .handle subject arms => .handle (refPatsExpr id uniq which subject) (arms.map (refPatsClause id uniq which))
  | .labelScope l body => .labelScope l (body.map (refPatsStmt id uniq which))
  | .deref e => .deref (refPatsExpr id uniq which e)
  | .reborrow u e => .reborrow u (refPatsExpr id uniq which e)
  | .fieldOf i e name => .fieldOf i (refPatsExpr id uniq which e) name
  | e => e

partial def refPatsClause (id : Nat) (uniq : Bool) (which : List Nat) : Clause → Clause
  | .mk pats body => .mk pats (body.map (refPatsStmt id uniq which))

partial def refPatsStmt (id : Nat) (uniq : Bool) (which : List Nat) : Stmt → Stmt
  | .let_ pat value => .let_ pat (refPatsExpr id uniq which value)
  | .expr e => .expr (refPatsExpr id uniq which e)
  | .defer e => .defer (refPatsExpr id uniq which e)
  | .letMut x value => .letMut x (refPatsExpr id uniq which value)
  | .assign target value => .assign (refPatsExpr id uniq which target) (refPatsExpr id uniq which value)
  | .located line col s => .located line col (refPatsStmt id uniq which s)

end

/-- A program with the first patterns of one callable's clauses written
`&Pattern`. -/
partial def refPatsItems (id : Nat) (uniq : Bool) (which : List Nat) (items : List Item) : List Item :=
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map (refPatsClause id uniq which))
    | .impl ps tr head args context methods => .impl ps tr head args context (refPatsItems id uniq which methods)
    | .traitInfo n supers defaults params assocs => .traitInfo n supers (refPatsItems id uniq which defaults) params assocs
    | .module name (some body) => .module name (some (refPatsItems id uniq which body))
    | .pub parent item => .pub parent ((refPatsItems id uniq which [item]).headD item)
    | item => item

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

mutual

partial def dotOwnExpr (call : Nat) (fn : String) : Expr → Expr
  | .call i f args =>
    let args := args.map (dotOwnExpr call fn)
    match f with
    | .fieldOf fi recv name =>
      let recv := dotOwnExpr call fn recv
      if i == call then .call i (.fieldOf fi recv ("%own:" ++ fn)) args
      else .call i (.fieldOf fi recv name) args
    | f => .call i (dotOwnExpr call fn f) args
  | .tailCall i f args => .tailCall i (dotOwnExpr call fn f) (args.map (dotOwnExpr call fn))
  | .tuple args => .tuple (args.map (dotOwnExpr call fn))
  | .proj e n => .proj (dotOwnExpr call fn e) n
  | .closure i clauses => .closure i (clauses.map (dotOwnClause call fn))
  | .handle subject arms => .handle (dotOwnExpr call fn subject) (arms.map (dotOwnClause call fn))
  | .labelScope l body => .labelScope l (body.map (dotOwnStmt call fn))
  | .deref e => .deref (dotOwnExpr call fn e)
  | .reborrow u e => .reborrow u (dotOwnExpr call fn e)
  | .fieldOf i e name => .fieldOf i (dotOwnExpr call fn e) name
  | e => e

partial def dotOwnClause (call : Nat) (fn : String) : Clause → Clause
  | .mk pats body => .mk pats (body.map (dotOwnStmt call fn))

partial def dotOwnStmt (call : Nat) (fn : String) : Stmt → Stmt
  | .let_ pat value => .let_ pat (dotOwnExpr call fn value)
  | .expr e => .expr (dotOwnExpr call fn e)
  | .defer e => .defer (dotOwnExpr call fn e)
  | .letMut x value => .letMut x (dotOwnExpr call fn value)
  | .assign target value => .assign (dotOwnExpr call fn target) (dotOwnExpr call fn value)
  | .located line col s => .located line col (dotOwnStmt call fn s)

end

partial def dotOwnItems (call : Nat) (fn : String) (items : List Item) : List Item :=
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map (dotOwnClause call fn))
    | .impl ps tr head args context methods => .impl ps tr head args context (dotOwnItems call fn methods)
    | .traitInfo n supers defaults params assocs => .traitInfo n supers (dotOwnItems call fn defaults) params assocs
    | .module name (some body) => .module name (some (dotOwnItems call fn body))
    | .pub parent item => .pub parent ((dotOwnItems call fn [item]).headD item)
    | item => item

/-- A program with the arguments the checker chose to give as other than
written (`Blocks.argsChosen`) written in. -/
partial def argsChosenExpr (picks : List ((Nat × Nat) × Expr)) : Expr → Expr
  | .call i f args =>
    let args := (args.map (argsChosenExpr picks)).zipIdx.map fun (a, k) =>
      (picks.lookup (i, k)).getD a
    .call i (argsChosenExpr picks f) args
  | .tailCall i f args => .tailCall i (argsChosenExpr picks f) (args.map (argsChosenExpr picks))
  | .tuple args => .tuple (args.map (argsChosenExpr picks))
  | .proj e n => .proj (argsChosenExpr picks e) n
  | .closure i clauses => .closure i (clauses.map fun
    | .mk pats body => .mk pats (body.map (argsChosenStmt picks)))
  | .handle subject arms => .handle (argsChosenExpr picks subject) (arms.map fun
    | .mk pats body => .mk pats (body.map (argsChosenStmt picks)))
  | .labelScope l body => .labelScope l (body.map (argsChosenStmt picks))
  | .deref e => .deref (argsChosenExpr picks e)
  | .reborrow u e => .reborrow u (argsChosenExpr picks e)
  | .fieldOf i e name => .fieldOf i (argsChosenExpr picks e) name
  | e => e
where
  argsChosenStmt (picks : List ((Nat × Nat) × Expr)) : Stmt → Stmt
    | .let_ pat value => .let_ pat (argsChosenExpr picks value)
    | .expr e => .expr (argsChosenExpr picks e)
    | .defer e => .defer (argsChosenExpr picks e)
    | .letMut x value => .letMut x (argsChosenExpr picks value)
    | .assign target value => .assign (argsChosenExpr picks target) (argsChosenExpr picks value)
    | .located line col s => .located line col (argsChosenStmt picks s)

partial def argsChosenItems (picks : List ((Nat × Nat) × Expr)) (items : List Item) : List Item :=
  if picks.isEmpty then items else
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map fun
      | .mk pats body => .mk pats (body.map (argsChosenExpr.argsChosenStmt picks)))
    | .impl ps tr head args context methods => .impl ps tr head args context (argsChosenItems picks methods)
    | .traitInfo n supers defaults params assocs => .traitInfo n supers (argsChosenItems picks defaults) params assocs
    | .module name (some body) => .module name (some (argsChosenItems picks body))
    | .pub parent item => .pub parent ((argsChosenItems picks [item]).headD item)
    | item => item

/-- A program with the functions of dot calls the checker chose by the
value's type (`Blocks.dotChosen`) written in. -/
partial def chosenExpr (picks : List (Nat × String × Nat)) : Expr → Expr
  | .call i f args =>
    let args := args.map (chosenExpr picks)
    match f, picks.lookup i with
    | .name _ _, some (fn, how) =>
      let args := match how, args with
        | 0, _ => args
        | k, .name none v :: rest => .ref (k == 2) v :: rest
        | _, _ => args
      .call i (.name none fn) args
    | f, _ => .call i (chosenExpr picks f) args
  | .tailCall i f args => .tailCall i (chosenExpr picks f) (args.map (chosenExpr picks))
  | .tuple args => .tuple (args.map (chosenExpr picks))
  | .proj e n => .proj (chosenExpr picks e) n
  | .closure i clauses => .closure i (clauses.map fun
    | .mk pats body => .mk pats (body.map (chosenStmt picks)))
  | .handle subject arms => .handle (chosenExpr picks subject) (arms.map fun
    | .mk pats body => .mk pats (body.map (chosenStmt picks)))
  | .labelScope l body => .labelScope l (body.map (chosenStmt picks))
  | .deref e => .deref (chosenExpr picks e)
  | .reborrow u e => .reborrow u (chosenExpr picks e)
  | .fieldOf i e name => .fieldOf i (chosenExpr picks e) name
  | e => e
where
  chosenStmt (picks : List (Nat × String × Nat)) : Stmt → Stmt
    | .let_ pat value => .let_ pat (chosenExpr picks value)
    | .expr e => .expr (chosenExpr picks e)
    | .defer e => .defer (chosenExpr picks e)
    | .letMut x value => .letMut x (chosenExpr picks value)
    | .assign target value => .assign (chosenExpr picks target) (chosenExpr picks value)
    | .located line col s => .located line col (chosenStmt picks s)

partial def chosenItems (picks : List (Nat × String × Nat)) (items : List Item) : List Item :=
  if picks.isEmpty then items else
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map fun
      | .mk pats body => .mk pats (body.map (chosenExpr.chosenStmt picks)))
    | .impl ps tr head args context methods => .impl ps tr head args context (chosenItems picks methods)
    | .traitInfo n supers defaults params assocs => .traitInfo n supers (chosenItems picks defaults) params assocs
    | .module name (some body) => .module name (some (chosenItems picks body))
    | .pub parent item => .pub parent ((chosenItems picks [item]).headD item)
    | item => item

/-- A program with the receiver of one dot call, a name, borrowed:
`Syntax.recvRefMark`. -/
partial def recvRefExpr (call : Nat) (uniq : Bool) : Expr → Expr
  | .call i f args =>
    let args := args.map (recvRefExpr call uniq)
    match f with
    | .fieldOf fi (.name none x) name =>
      if i == call then .call i (.fieldOf fi (.ref uniq x) name) args
      else .call i (.fieldOf fi (.name none x) name) args
    | f => .call i (recvRefExpr call uniq f) args
  | .tailCall i f args => .tailCall i (recvRefExpr call uniq f) (args.map (recvRefExpr call uniq))
  | .tuple args => .tuple (args.map (recvRefExpr call uniq))
  | .proj e n => .proj (recvRefExpr call uniq e) n
  | .closure i clauses => .closure i (clauses.map fun
    | .mk pats body => .mk pats (body.map (recvRefStmt call uniq)))
  | .handle subject arms => .handle (recvRefExpr call uniq subject) (arms.map fun
    | .mk pats body => .mk pats (body.map (recvRefStmt call uniq)))
  | .labelScope l body => .labelScope l (body.map (recvRefStmt call uniq))
  | .deref e => .deref (recvRefExpr call uniq e)
  | .reborrow u e => .reborrow u (recvRefExpr call uniq e)
  | .fieldOf i e name => .fieldOf i (recvRefExpr call uniq e) name
  | e => e
where
  recvRefStmt (call : Nat) (uniq : Bool) : Stmt → Stmt
    | .let_ pat value => .let_ pat (recvRefExpr call uniq value)
    | .expr e => .expr (recvRefExpr call uniq e)
    | .defer e => .defer (recvRefExpr call uniq e)
    | .letMut x value => .letMut x (recvRefExpr call uniq value)
    | .assign target value => .assign (recvRefExpr call uniq target) (recvRefExpr call uniq value)
    | .located line col s => .located line col (recvRefStmt call uniq s)

partial def recvRefItems (call : Nat) (uniq : Bool) (items : List Item) : List Item :=
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map fun
      | .mk pats body => .mk pats (body.map (recvRefExpr.recvRefStmt call uniq)))
    | .impl ps tr head args context methods => .impl ps tr head args context (recvRefItems call uniq methods)
    | .traitInfo n supers defaults params assocs => .traitInfo n supers (recvRefItems call uniq defaults) params assocs
    | .module name (some body) => .module name (some (recvRefItems call uniq body))
    | .pub parent item => .pub parent ((recvRefItems call uniq [item]).headD item)
    | item => item

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

mutual

partial def letMutExpr (line col : Nat) (x : String) : Expr → Expr
  | .call i f args => .call i (letMutExpr line col x f) (args.map (letMutExpr line col x))
  | .tailCall i f args => .tailCall i (letMutExpr line col x f) (args.map (letMutExpr line col x))
  | .tuple args => .tuple (args.map (letMutExpr line col x))
  | .proj e n => .proj (letMutExpr line col x e) n
  | .closure i clauses => .closure i (clauses.map (letMutClause line col x))
  | .handle subject arms => .handle (letMutExpr line col x subject) (arms.map (letMutClause line col x))
  | .labelScope l body => .labelScope l (letMutStmts line col x body)
  | .deref e => .deref (letMutExpr line col x e)
  | .reborrow uniq e => .reborrow uniq (letMutExpr line col x e)
  | .fieldOf i e name => .fieldOf i (letMutExpr line col x e) name
  | e => e

/-- A clause; at place `0:0`, one that takes `x` as a parameter (or a name
its patterns bind) starts by keeping it in a variable, written at the place
of its first statement. -/
partial def letMutClause (line col : Nat) (x : String) : Clause → Clause
  | .mk pats body =>
    let body := letMutStmts line col x body
    if line == 0 && col == 0 && (pats.flatMap patVars).contains x then
      match body with
      | .located l c s :: rest => .mk pats (.located l c (.letMut x (.name none x)) :: .located l c s :: rest)
      | _ => .mk pats body
    else .mk pats body

partial def letMutStmts (line col : Nat) (x : String) : List Stmt → List Stmt
  | [] => []
  | .located l c (.let_ pat value) :: rest =>
    let value := letMutExpr line col x value
    let rest := letMutStmts line col x rest
    if l == line && c == col then
      match pat with
      | .var y =>
        if y == x then .located l c (.letMut y value) :: rest
        else .located l c (.let_ pat value) :: rest
      | _ =>
        -- (A name a pattern binds: kept in a variable straight after.)
        if (patVars pat).contains x then
          .located l c (.let_ pat value) :: .located l c (.letMut x (.name none x)) :: rest
        else .located l c (.let_ pat value) :: rest
    else .located l c (.let_ pat value) :: rest
  | s :: rest => letMutStmt line col x s :: letMutStmts line col x rest

partial def letMutStmt (line col : Nat) (x : String) : Stmt → Stmt
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
  let fn := fun (clauses : List Clause) =>
    let after := clauses.map (etaClause x arity base)
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

mutual

partial def splitExpr (x : String) (sp : Split) : Expr → Expr
  | .proj (.name none y) i =>
    if y == x && i < sp.fields.length then .name none (sp.var x i) else .proj (.name none y) i
  | .fieldOf id (.name none y) s =>
    match sp.index s, y == x with
    | some i, true => .name none (sp.var x i)
    | _, _ => .fieldOf id (.name none y) s
  | .refField id uniq y (s :: path) star =>
    match sp.index s, y == x && !star with
    | some i, true =>
      if path.isEmpty then .ref uniq (sp.var x i) else .refField id uniq (sp.var x i) path false
    | _, _ => .refField id uniq y (s :: path) star
  | .name none y =>
    if y == x then sp.make ((List.range sp.fields.length).map fun i => .name none (sp.var x i))
    else .name none y
  | .call i f args => .call i (splitExpr x sp f) (args.map (splitExpr x sp))
  | .tailCall i f args => .tailCall i (splitExpr x sp f) (args.map (splitExpr x sp))
  | .tuple args => .tuple (args.map (splitExpr x sp))
  | .proj e i => .proj (splitExpr x sp e) i
  | .closure i clauses => .closure i (clauses.map (splitClause x sp))
  | .handle subject arms => .handle (splitExpr x sp subject) (arms.map (splitClause x sp))
  | .labelScope l body => .labelScope l (splitStmts x sp body)
  | .deref e => .deref (splitExpr x sp e)
  | .reborrow uniq e => .reborrow uniq (splitExpr x sp e)
  | .fieldOf i e name => .fieldOf i (splitExpr x sp e) name
  | e => e

partial def splitClause (x : String) (sp : Split) : Clause → Clause
  | .mk pats body => if (pats.flatMap patVars).contains x then .mk pats body else .mk pats (splitStmts x sp body)

/-- The statements after `x` is made, with its fields as variables of their
own, up to where a name `x` is made again. -/
partial def splitStmts (x : String) (sp : Split) : List Stmt → List Stmt
  | [] => []
  | .located l c s :: rest =>
    match splitStmts x sp (s :: rest) with
    | first :: more => .located l c first :: more
    | [] => []
  | .let_ pat value :: rest =>
    let value := splitExpr x sp value
    if (patVars pat).contains x then .let_ pat value :: rest
    else .let_ pat value :: splitStmts x sp rest
  | .letMut y value :: rest =>
    let value := splitExpr x sp value
    if y == x then .letMut y value :: rest
    else .letMut y value :: splitStmts x sp rest
  | .assign (.name none y) value :: rest =>
    if y == x then
      -- (Assigning the whole: its parts, each to its variable.)
      let parts := (List.range sp.fields.length).map fun i => s!"%{sp.var x i}"
      .let_ (sp.apart (parts.map Pattern.var)) (splitExpr x sp value)
        :: (parts.zipIdx.map fun (p, i) => Stmt.assign (.name none (sp.var x i)) (.name none p))
        ++ splitStmts x sp rest
    else .assign (.name none y) (splitExpr x sp value) :: splitStmts x sp rest
  | .assign target value :: rest =>
    .assign (splitExpr x sp target) (splitExpr x sp value) :: splitStmts x sp rest
  | .expr e :: rest => .expr (splitExpr x sp e) :: splitStmts x sp rest
  | .defer e :: rest => .defer (splitExpr x sp e) :: splitStmts x sp rest

end

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

mutual

/-- Every variable of these statements whose fields are borrowed, and that is
used no other way than its fields and its whole value are, made one variable
per field. -/
partial def splitFieldVars (structs : Structs) : List Stmt → List Stmt
  | [] => []
  | .located l c (.letMut x value) :: rest =>
    match splitOf structs value with
    | some (sp, es) =>
      let split := splitStmts x sp rest
      -- (Kept as it is where it is used some other way: borrowed whole, say.)
      if fieldBorrowed x rest && !(fvStmts [] split).contains x then
        (es.zipIdx.map fun (e, i) => Stmt.located l c (.letMut (sp.var x i) (splitFieldsExpr structs e)))
          ++ splitFieldVars structs split
      else .located l c (.letMut x (splitFieldsExpr structs value)) :: splitFieldVars structs rest
    | none => .located l c (.letMut x (splitFieldsExpr structs value)) :: splitFieldVars structs rest
  | .located l c s :: rest =>
    match splitFieldVars structs [s] with
    | [s'] => .located l c s' :: splitFieldVars structs rest
    | ss => ss.map (Stmt.located l c) ++ splitFieldVars structs rest
  | .let_ pat value :: rest => .let_ pat (splitFieldsExpr structs value) :: splitFieldVars structs rest
  | .letMut x value :: rest => .letMut x (splitFieldsExpr structs value) :: splitFieldVars structs rest
  | .assign target value :: rest =>
    .assign (splitFieldsExpr structs target) (splitFieldsExpr structs value) :: splitFieldVars structs rest
  | .expr e :: rest => .expr (splitFieldsExpr structs e) :: splitFieldVars structs rest
  | .defer e :: rest => .defer (splitFieldsExpr structs e) :: splitFieldVars structs rest

partial def splitFieldsExpr (structs : Structs) : Expr → Expr
  | .call i f args => .call i (splitFieldsExpr structs f) (args.map (splitFieldsExpr structs))
  | .tailCall i f args => .tailCall i (splitFieldsExpr structs f) (args.map (splitFieldsExpr structs))
  | .tuple args => .tuple (args.map (splitFieldsExpr structs))
  | .proj e i => .proj (splitFieldsExpr structs e) i
  | .closure i clauses => .closure i (clauses.map fun
      | .mk pats body => .mk pats (splitFieldVars structs body))
  | .handle subject arms => .handle (splitFieldsExpr structs subject) (arms.map fun
      | .mk pats body => .mk pats (splitFieldVars structs body))
  | .labelScope l body => .labelScope l (splitFieldVars structs body)
  | .deref e => .deref (splitFieldsExpr structs e)
  | .reborrow uniq e => .reborrow uniq (splitFieldsExpr structs e)
  | .fieldOf i e name => .fieldOf i (splitFieldsExpr structs e) name
  | e => e

end

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
  let clause := fun (c : Clause) => match c with
    | .mk pats body => Clause.mk pats (splitFieldVars structs body)
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map clause)
    | .impl ps tr head args context methods => .impl ps tr head args context (methods.map fun
        | .fn m mps annots ret clauses => .fn m mps annots ret (clauses.map clause)
        | item => item)
    | item => item

end Glorious.Elab
