module

public import Glorious.Elab.Base
public import Glorious.Syntax.Resolve
public import Glorious.Addr

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

/-- The copies asked for: each by its name, with the function it is of, the
implementations it is for, and whether their places are dropped. An
implementation with nothing left to be known is a number here (`pool`: its
function and its parts' numbers; `byId` back), and stands in a body being
written out as a name of its own (`%known#n`) until it is called or taken
apart: so a copy is found, and a body written out, without implementations
written out and looked at again and again. -/
structure Copies where
  pool : Std.HashMap (String × List Nat) Nat := {}
  byId : Array (String × List Nat) := #[]
  byKey : Std.HashMap (String × List Nat × Bool) String := {}
  /-- Each copy by its name: the function it is of, the implementations it
  is for, and whether their places are dropped. -/
  byName : Std.HashMap String (String × List Nat × Bool) := {}
  /-- What `askCopy` added, in order (`LowerKept`). -/
  asked : Array ((String × List Nat × Bool) × String) := #[]

def internId (f : String) (ids : List Nat) : StateM Copies Nat := do
  match (← get).pool[(f, ids)]? with
  | some n => pure n
  | none =>
    let n := (← get).byId.size
    modify fun c => { c with pool := c.pool.insert (f, ids) n, byId := c.byId.push (f, ids) }
    pure n

/-- A body being written out for implementations, with the copies asked. -/
abbrev SpecM := StateT Flat.Body (StateM Copies)

def specPush (n : Flat.FExpr) : SpecM Flat.ExprId := modifyGet fun b => b.add n
def specPushS (n : Flat.FStmt) : SpecM Flat.StmtId := modifyGet fun b => (b.stmts.size, { b with stmts := b.stmts.push n })
def specPushC (n : Flat.FClause) : SpecM Flat.ClauseId := modifyGet fun b => (b.clauses.size, { b with clauses := b.clauses.push n })

/-- The number a name `%known#n` stands for. -/
def dictRefOfName? (x : String) : Option Nat :=
  if x.startsWith "%known#" then (x.drop 7).toString.toNat? else none

/-- The number of an implementation with nothing left to be known; none for
anything else. -/
partial def dictId (impls : Std.HashMap String ImplE) (e : Flat.ExprId) : SpecM (Option Nat) := do
  let b ← get
  if let some x := b.bare? e then
    if let some n := dictRefOfName? x then return some n
  match b.expr e with
  | .call _ fe subs =>
    let some f := b.bare? fe | return none
    unless impls.contains f do return none
    let mut ids := #[]
    for sub in subs do
      let some n ← dictId impls sub | return none
      ids := ids.push n
    some <$> (internId f ids.toList : StateM Copies Nat)
  | _ => pure none

/-- The implementation a number is, written out. -/
partial def dictExprOf (byId : Array (String × List Nat)) (n : Nat) : Expr :=
  match byId[n]? with
  | some (f, ids) => .call 0 (.name none f) (ids.map (dictExprOf byId))
  | none => .tuple []

def askCopy (fn : String) (ids : List Nat) (drop : Bool) : StateM Copies String := do
  let key := (fn, ids, drop)
  if let some name := (← get).byKey[key]? then return name
  let name := s!"{fn}⟨{",".intercalate (ids.map toString)}⟩{if drop then "'" else ""}"
  modify fun c => { c with byKey := c.byKey.insert key name, byName := c.byName.insert name key
                           asked := c.asked.push (key, name) }
  pure name

/-- Which of the prelude's spreads `g` is. -/
def spreadKind (g : String) : Option String :=
  if g == "spread_split" || g == "spread_split_as" then some "split"
  else if g == "spread_cons" || g == "spread_cons_as" then some "cons"
  else if g == "spread_snoc" || g == "spread_snoc_as" then some "snoc"
  else if g == "spread_call" || g == "spread_call_as" then some "call"
  else none

/-- How long a list is, by the implementation of `Spread` it has: one for
`()`, or one for its first and rest given the rest's. -/
def spreadLength (byId : Array (String × List Nat)) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match byId[i]? with
    | some (f, []) => if f.startsWith (implDictName "Spread" "") then some 0 else none
    -- (The rest's `Spread` first; after it, how what is held is destroyed,
    -- where the program asks that of the parts too.)
    | some (f, j :: _) =>
      if f.startsWith (implDictName "Spread" "") then (spreadLength byId j fuel).map (· + 1) else none
    | _ => none

/-- What is called and what it is given, at a call. -/
def specCall (tr : TraitInfo) (go : Flat.FGoM (StateM Copies)) (f : Flat.ExprId) (args : Array Flat.ExprId) :
    SpecM (Flat.ExprId × Array Flat.ExprId) := do
  let args ← args.mapM go.ex
  match (← get).expr f with
  | .proj d idx =>
    -- A trait's function taken out of an implementation that is known: the
    -- implementation's function, for what its own conditions are met by.
    let d ← go.ex d
    let kept := fun (_ : Unit) => (do
      if d == (match (← get).expr f with | .proj d0 _ => d0 | _ => d) then pure (f, args)
      else pure (← specPush (.proj d idx), args) : SpecM (Flat.ExprId × Array Flat.ExprId))
    match ← dictId tr.implsAt d with
    | some n =>
      match (← getThe Copies).byId[n]? with
      | some (dictFn, subs) =>
        match (tr.implsAt[dictFn]?).bind (·.methods[idx]?) with
        | some (fn, _) =>
          if subs.isEmpty then pure (← specPush (.name none fn), args)
          else pure (← specPush (.name none (← (askCopy fn subs true : StateM Copies String))), args)
        | none => kept ()
      | none => kept ()
    | none => kept ()
  | .name none g =>
    -- (A list of values spread, `Prelude`'s `spread_split`, `spread_cons`
    -- and `spread_snoc`: written out for its length, known from how the
    -- list has `Spread`: one implementation for each of its parts.)
    if let some kind := spreadKind g then
      let bounds := (tr.boundedAt[g]?).getD 0
      for k in [0:bounds] do
        if let some d := args[k]? then
          if let some i ← dictId tr.implsAt d then
            if let some n := spreadLength (← getThe Copies).byId i 4096 then
              return (← specPush (.name none s!"%spread_{kind}#{n}"), args.extract bounds args.size)
    let n := (tr.boundedAt[g]?).getD 0
    if n > 0 && args.size ≥ n then
      let mut ids : Array Nat := #[]
      for a in args.extract 0 n do
        if let some i ← dictId tr.implsAt a then ids := ids.push i
      if ids.size == n then
        let copy ← (askCopy g ids.toList false : StateM Copies String)
        let unit ← (List.range n).mapM fun _ => specPush (.tuple #[])
        return (← specPush (.name none copy), unit.toArray ++ args.extract n args.size)
    pure (f, args)
  | _ => do pure (← go.ex f, args)

/-- A function written out for the implementations `known` (by the names its
parameters for them had, each the name it stands as): each call sent where
`specCall` says. -/
def specRewrite (tr : TraitInfo) (known : List (String × String)) : Flat.FRewriteM (StateM Copies) where
  onExpr go b e := match b.expr e with
    | .name none x => (known.lookup x).map fun y => specPush (.name none y)
    | .call id f args => some do
      let (f', args') ← specCall tr go f args
      if f' == f && args' == args then pure e else specPush (.call id f' args')
    | .tailCall id f args => some do
      let (f', args') ← specCall tr go f args
      if f' == f && args' == args then pure e else specPush (.tailCall id f' args')
    | _ => none

/-- A function given no implementation, with the calls in it sent to copies. -/
def specRoot (tr : TraitInfo) (item : Syntax.Item) : StateM Copies Syntax.Item :=
  match item with
  | .fn name ps annots ret b =>
    if (tr.boundedAt[name]?).getD 0 == 0 then do
      let (roots, b) ← (b.roots.mapM (specRewrite tr []).clause).run b
      pure (.fn name ps annots ret { b with roots })
    else pure item
  | other => pure other

/-- Does an expression name the label `l`? -/
partial def namesLabel (b : Flat.Body) (l : String) (e : Flat.ExprId) : Bool :=
  match b.expr e with
  | .label x => x == l
  | .labelScope x body => x != l && body.any fun s => (b.stmtExprs s).any (namesLabel b l)
  | _ => (b.children e).any (namesLabel b l)

def stmtNamesLabel (b : Flat.Body) (l : String) (s : Flat.StmtId) : Bool := (b.stmtExprs s).any (namesLabel b l)

/-- Each `%known#n` left in a body, written out as the implementation. -/
def unrefBody (byId : Array (String × List Nat)) (b : Flat.Body) : Flat.Body :=
  let r : Flat.FRewrite := { onExpr := fun _ b e =>
    (b.bare? e >>= dictRefOfName?).map fun n => Flat.flatExpr (dictExprOf byId n) }
  r.body b

/-- A clause of a copy: the parameters for implementations dropped, or each
taking `()`, and the body written out for the implementations. -/
def specCopyClause (tr : TraitInfo) (known : List (String × String)) (n : Nat) (drop : Bool)
    (fn : String) (clause : Flat.ClauseId) : SpecM Flat.ClauseId := do
  let ⟨pats, body⟩ := (← get).clause clause
  let pats := if drop then pats.drop n else List.replicate n Pattern.wild ++ pats.drop n
  let body ← body.mapM (specRewrite tr known).st
  -- (A function's name is the label its body leaves by, `@find(..)`: the
  -- copy has another name, so its body is given that label.)
  let b ← get
  let body ← if body.any (stmtNamesLabel b fn) then do
      let scope ← specPush (.labelScope fn body)
      pure #[← specPushS (.expr scope)]
    else pure body
  specPushC ⟨pats, body⟩

/-- The copy of a function (`item`, without traits) for the implementations
`dicts`, named `name`, their places dropped if `drop`. -/
def specCopy (tr : TraitInfo) (name : String) (dicts : List Nat) (drop : Bool) :
    Syntax.Item → StateM Copies (Option Syntax.Item)
  | .fn fn ps annots ret b => do
    let n := dicts.length
    let known : List (String × String) :=
      (List.range n).map fun k => (s!"%dict{k}", s!"%known#{dicts[k]?.getD 0}")
    let (roots, b) ← (b.roots.mapM (specCopyClause tr known n drop fn)).run b
    let annots := if drop then annots.drop n else annots
    pure (some (.fn name ps annots ret { b with roots }))
  | _ => pure none

/-! ## Constants worked out once

After the copies are made, a trait's constant at a known type is a call of a
function that takes nothing: `<B1<B0<Z>> as Known>::VALUE` is a function
that adds one to twice another. Such a function whose body is integer
arithmetic of numbers and of such calls has its number worked out here, and
every call of it is that number. A result that does not fit in 64 bits is
left to go wrong when the program runs, as it would have. -/

/-- A function's one clause, if its body is one expression: its patterns and
the expression. -/
def oneExpr (b : Flat.Body) : Option (List Pattern × Flat.ExprId) :=
  match b.roots with
  | #[c] =>
    let ⟨pats, body⟩ := b.clause c
    match body with
    | #[s] =>
      match b.stmt s with
      | .expr e => some (pats, e)
      | .located _ _ inner =>
        match b.stmt inner with
        | .expr e => some (pats, e)
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- The number an expression stands for, given the numbers of the names in
`env` and the functions `fns`, if it is one: numbers, `int_add`, `int_sub`
and `int_mul` of numbers, and calls of functions whose one clause takes plain
names and is one expression. `fuel` bounds the calls followed. -/
partial def foldInt (fns : Std.HashMap String Flat.Body) (env : List (String × Int)) (fuel : Nat)
    (b : Flat.Body) (e : Flat.ExprId) : Option Int :=
  match b.expr e with
  | .int n => some n
  | .name none x => env.lookup x
  | .call _ fe args => do
    let f ← b.bare? fe
    if fuel == 0 then none
    -- (A type written for a value, or for a function's parameters, says
    -- nothing of its number.)
    if f == Syntax.ascribeMark || f == Syntax.instMark then
      match args[0]? with
      | some a => foldInt fns env (fuel - 1) b a
      | none => none
    else
      let vals ← args.toList.mapM (foldInt fns env (fuel - 1) b)
      let fits := fun (n : Int) =>
        if -9223372036854775808 ≤ n && n ≤ 9223372036854775807 then some n else none
      match f, vals with
      | "int_add", [x, y] => fits (x + y)
      | "int_sub", [x, y] => fits (x - y)
      | "int_mul", [x, y] => fits (x * y)
      | _, _ =>
        match fns[f]? with
        | some fb =>
          match oneExpr fb with
          | some (pats, body) =>
            let names ← pats.mapM fun
              | .var x => some x
              | _ => none
            if names.length != vals.length then none
            else foldInt fns (names.zip vals) (fuel - 1) fb body
          | none => none
        | none => none
  | _ => none

/-- Each call of a function that takes nothing and works out to a number
(`known`) written as that number. -/
def foldRewrite (known : Std.HashMap String Int) : Flat.FRewrite where
  onExpr _ b e :=
    match b.expr e with
    | .call id fe args =>
      match b.bare? fe, args.toList with
      | some f, [] => known[f]?.map fun n => Flat.pushExpr (.int n)
      | some mark, inner :: rest =>
        match b.expr inner with
        | .call _ g #[] =>
          match b.bare? g >>= (known[·]?) with
          | some n =>
            if mark == Syntax.instMark then some (Flat.pushExpr (.int n))
            else some (do
              let v ← Flat.pushExpr (.int n)
              Flat.pushExpr (.call id fe (#[v] ++ rest.toArray)))
          | none => none
        | _ => none
      | _, _ => none
    | _ => none

/-- A program with every call of a function that takes nothing and works out
to a number written as that number. -/
def foldConstants (items : List Syntax.Item) : List Syntax.Item :=
  let fns : Std.HashMap String Flat.Body := items.foldl (init := {}) fun m item => match item with
    | .fn name _ _ _ b => m.insertIfNew name b
    | _ => m
  let known : Std.HashMap String Int := items.foldl (init := {}) fun m item => match item with
    | .fn name _ _ _ b =>
      match oneExpr b with
      | some ([], body) => match foldInt fns [] 64 b body with
        | some n => m.insertIfNew name n
        | none => m
      | _ => m
    | _ => m
  if known.isEmpty then items else
  items.map fun
    | .fn name ps annots ret b =>
      -- (Only the functions that call one are written again.)
      let calls := fun (n : Flat.FExpr) => match n with
        | .call _ fe #[] => (b.bare? fe).any known.contains
        | _ => false
      if b.roots.any (b.anyClause calls) then .fn name ps annots ret ((foldRewrite known).body b)
      else .fn name ps annots ret b
    | item => item

/-! ## `..` in a tuple pattern

How many parts the `..` of `(first, ..)` stands for is known once the
tuple's type is. The checker says so, and the program is then read with that
many `_` written in its place. -/


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
  make : Array Flat.ExprId → Flat.Build Flat.ExprId
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
def splitRewrite (x : String) (sp : Split) : Flat.FRewrite where
  onExpr _ b e :=
    match b.expr e with
    | .proj e' i =>
      if b.bare? e' == some x && i < sp.fields.length then some (Flat.pushExpr (.name none (sp.var x i))) else none
    | .fieldOf _ e' s =>
      match sp.index s, b.bare? e' == some x with
      | some i, true => some (Flat.pushExpr (.name none (sp.var x i)))
      | _, _ => none
    | .refField id uniq y (s :: path) star =>
      match sp.index s, y == x && !star with
      | some i, true =>
        some (Flat.pushExpr (if path.isEmpty then .ref uniq (sp.var x i) else .refField id uniq (sp.var x i) path false))
      | _, _ => none
    | .name none y =>
      if y == x then some (do
        let parts ← (List.range sp.fields.length).toArray.mapM fun i => Flat.pushExpr (.name none (sp.var x i))
        sp.make parts)
      else none
    | _ => none
  onClause _ b c :=
    if ((b.clause c).pats.flatMap Elab.patVars).contains x then some (pure c) else none
  onStmts go b ss :=
    match ss with
    | s :: rest =>
      match b.stmt s with
      | .located l c inner => some (do
        match ← go.stmts (inner :: rest) with
        | first :: more => pure ((← Flat.pushStmt (.located l c first)) :: more)
        | [] => pure [])
      | .let_ pat value =>
        if (Elab.patVars pat).contains x then some (do pure ((← Flat.pushStmt (.let_ pat (← go.ex value))) :: rest)) else none
      | .letMut y value =>
        if y == x then some (do pure ((← Flat.pushStmt (.letMut y (← go.ex value))) :: rest)) else none
      | .assign target value =>
        if b.bare? target != some x then none else some (do
          -- (Assigning the whole: its parts, each to its variable.)
          let parts := (List.range sp.fields.length).map fun i => s!"%{sp.var x i}"
          let first ← Flat.pushStmt (.let_ (sp.apart (parts.map Pattern.var)) (← go.ex value))
          let mut assigns : List Flat.StmtId := []
          for (p, i) in parts.zipIdx do
            let t ← Flat.pushExpr (.name none (sp.var x i))
            let v ← Flat.pushExpr (.name none p)
            assigns := assigns ++ [← Flat.pushStmt (.assign t v)]
          pure (first :: assigns ++ (← go.stmts rest)))
      | _ => none
    | [] => none

open Flat in
/-- Does `x` have a field borrowed in these statements, before it is made again? -/
partial def fieldBorrowed (b : Body) (x : String) (stmts : List StmtId) : Bool :=
  let rec inExpr (e : ExprId) : Bool :=
    match b.expr e with
    | .refField _ _ y (_ :: _) false => y == x
    | .call _ f args | .tailCall _ f args => inExpr f || args.any inExpr
    | .tuple args => args.any inExpr
    | .proj e _ | .deref e | .reborrow _ e | .fieldOf _ e _ => inExpr e
    | .closure _ clauses | .handle _ clauses =>
      (match b.expr e with | .handle s _ => inExpr s | _ => false) ||
      clauses.any fun c =>
        let ⟨pats, body⟩ := b.clause c
        !(pats.flatMap Elab.patVars).contains x && fieldBorrowed b x body.toList
    | .labelScope _ body => fieldBorrowed b x body.toList
    | _ => false
  match stmts with
  | [] => false
  | s :: rest =>
    match b.stmt s with
    | .located _ _ inner => fieldBorrowed b x (inner :: rest)
    | .let_ pat value => inExpr value || (!(Elab.patVars pat).contains x && fieldBorrowed b x rest)
    | .letMut y value => inExpr value || (y != x && fieldBorrowed b x rest)
    | .assign target value => inExpr target || inExpr value || fieldBorrowed b x rest
    | .expr e | .defer e => inExpr e || fieldBorrowed b x rest

/-- The structs whose variables can be split: each constructor with its
fields' names, for those without `Drop` (whose value is taken apart only by
its own `drop`). -/
abbrev Structs := List (String × List String)

/-- How a variable made by this value would be split, if it can be. -/
def splitOf (structs : Structs) (b : Flat.Body) (e : Flat.ExprId) : Option (Split × Array Flat.ExprId) :=
  match b.expr e with
  | .tuple es =>
    if es.size ≥ 2 then
      some (⟨(List.range es.size).map toString, fun vs => Flat.pushExpr (.tuple vs), .tuple⟩, es)
    else none
  | .call _ f args =>
    match b.expr f with
    | .name q s =>
      match structs.lookup s with
      | some names =>
        if names.length ≥ 2 && names.length == args.size then
          some (⟨names, fun vs => do Flat.pushExpr (.call 0 (← Flat.pushExpr (.name q s)) vs), fun ps => .ctor s q ps⟩, args)
        else none
      | none => none
    | _ => none
  | _ => none

/-- Every variable whose fields are borrowed, and that is used no other way
than its fields and its whole value are, made one variable per field. -/
def splitFieldsRewrite (structs : Structs) : Flat.FRewrite where
  onStmts go b ss :=
    match ss with
    | s :: rest =>
      match b.stmt s with
      | .located l c inner =>
        match b.stmt inner with
        | .letMut x value =>
          (splitOf structs b value).bind fun (sp, es) =>
            if !fieldBorrowed b x rest then none else
            let (b', split) := (splitRewrite x sp).stmts b rest
            -- (Kept as it is where it is used some other way: borrowed whole, say.)
            if (b'.fvStmts [] split).contains x then none else
            some (do
              set b'
              let mut lets : List Flat.StmtId := []
              for (e, i) in es.toList.zipIdx do
                let v ← Flat.pushStmt (.letMut (sp.var x i) (← go.ex e))
                lets := lets ++ [← Flat.pushStmt (.located l c v)]
              pure (lets ++ (← go.stmts split)))
        | _ => none
      | _ => none
    | [] => none

/-- A program's items with its variables whose fields are borrowed apart made
one variable per field (`splitFieldVars`); `all` are every item of the
program, for the structs and what has `Drop`. -/
def splitFieldItems (all items : List Syntax.Item) : List Syntax.Item :=
  let unwrap := fun (item : Syntax.Item) => match item with
    | .pub _ inner => inner
    | other => other
  let dropped := all.filterMap fun item => match unwrap item with
    | .impl _ tr head _ _ _ => if tr == "Drop" then some head else none
    | _ => none
  let structs : Structs := all.filterMap fun item => match unwrap item with
    | (.fieldNames ctor names _) => if dropped.contains ctor then none else some (ctor, names)
    | _ => none
  -- (Only a body with a field borrowed, `fieldBorrowed`, has one to split.)
  let borrowed := fun (n : Flat.FExpr) => match n with
    | .refField _ _ _ (_ :: _) false => true
    | _ => false
  let split := fun (b : Flat.Body) =>
    if b.exprs.any borrowed then (splitFieldsRewrite structs).body b else b
  items.map fun
    | .fn name ps annots ret b => .fn name ps annots ret (split b)
    | .impl ps tr head args context methods => .impl ps tr head args context (methods.map fun
        | .fn m mps annots ret b => .fn m mps annots ret (split b)
        | item => item)
    | item => item

/-! ## What the checker decided, written into a flat body -/


/-- A clause whose patterns bind `x` that starts by keeping it in a variable,
written at the place of its first statement (`letMutRewriteF`). -/
def heldFirst (x : String) : Flat.FRewrite where
  onClause go b c :=
    let ⟨pats, body⟩ := b.clause c
    if !(pats.flatMap patVars).contains x then none else some (do
      let body ← go.stmts body.toList
      match body with
      | first :: rest =>
        match (← get).stmt first with
        | .located l c _ =>
          let held ← Flat.pushStmt (.letMut x (← Flat.pushExpr (.name none x)))
          Flat.pushClause ⟨pats, ((← Flat.pushStmt (.located l c held)) :: first :: rest).toArray⟩
        | _ => Flat.pushClause ⟨pats, body.toArray⟩
      | [] => Flat.pushClause ⟨pats, #[]⟩)

/-- A value with a `drop` to run that one path uses and another does not is
kept in a variable, as `let mut` keeps it: where it was not used, the variable
destroys it. The checker says which `let`: the `let x` at `line:col` written
`let mut x`; a name a pattern binds kept in a variable straight after, or
where a clause of the statement there that binds it starts. At place `0:0`,
a clause that takes `x` as a parameter (or a name its patterns bind) starts
by keeping it in a variable, written at the place of its first statement. -/
def letMutRewriteF (line col : Nat) (x : String) : Flat.FRewrite where
  onStmts go b ss :=
    match ss with
    | s :: rest =>
      match b.stmt s with
      | .located l c inner =>
        if l != line || c != col then none else
        match b.stmt inner with
        | .let_ pat value =>
          some (do
            let value ← go.ex value
            let rest ← go.stmts rest
            match pat with
            | .var y =>
              if y == x then pure ((← Flat.pushStmt (.located l c (← Flat.pushStmt (.letMut y value)))) :: rest)
              else pure ((← Flat.pushStmt (.located l c (← Flat.pushStmt (.let_ pat value)))) :: rest)
            | _ =>
              let first ← Flat.pushStmt (.located l c (← Flat.pushStmt (.let_ pat value)))
              if (patVars pat).contains x then
                let held ← Flat.pushStmt (.letMut x (← Flat.pushExpr (.name none x)))
                pure (first :: (← Flat.pushStmt (.located l c held)) :: rest)
              else pure (first :: rest))
        -- (A name a clause in the statement binds, `A(name, n) => ..` of a
        -- `match`: kept in a variable where the clause starts.)
        | _ => some (do pure ((← (heldFirst x).st s) :: (← go.stmts rest)))
      | _ => none
    | [] => none
  onClause go b c :=
    if line != 0 || col != 0 then none else (heldFirst x).onClause go b c

/-- A function's body with one thing the checker wrote where it found it
written in alike: `name` is the name the function is checked by. (What
the checker only says to itself, to be written where it is, `receiver`,
`refPats` and `eta`, is never kept.) -/
def decideBody (d : Decision) (name : String) (b : Flat.Body) : Flat.Body :=
  match d with
  | .restHere id count => (restNode id count b).getD b
  | .letMut owner line col x => if name == owner then (letMutRewriteF line col x).body b else b
  | .receiverHere call fn borrow => (receiverNode call fn borrow b).getD b
  | .receiverTemp call fn uniq root => (receiverTempNode call fn uniq root b).getD b
  | .receiverField call fn uniq star => (receiverFieldNode call fn uniq star b).getD b
  | .receiverCopy call => (receiverCopyNode call b).getD b
  | .derefHere id borrow => (derefNode id borrow b).getD b
  | .derefAssignHere id borrow => (derefAssignNode id borrow b).getD b
  | .derefRefHere id uniq borrow => (derefRefNode id uniq borrow b).getD b
  | .compareHere call refs => (compareNode call refs b).getD b
  | .etaHere owner node x arity id => if name == owner then (etaNode node x arity id b).getD b else b
  | .refPatsHere id clauses => (refPatsNode id clauses b).getD b
  | .eta .. | .refPats .. | .receiver .. => b

/-- Every function of an item with what the checker decided written in, each
under the name it is checked by. -/
partial def Item.decide (f : String → List (Option TypeExpr) → Flat.Body → Flat.Body) : Syntax.Item → Syntax.Item
  | .fn name ps annots ret b => .fn name ps annots ret (f name annots b)
  | .impl ps tr head args ctx methods => .impl ps tr head args ctx (methods.map fun
    | .fn m mps annots ret b => .fn m mps annots ret (f (implFnName tr head m) annots b)
    | item => Item.decide f item)
  | .traitInfo n supers defaults ps assocs => .traitInfo n supers (defaults.map fun
    | .fn m mps annots ret b => .fn m mps annots ret (f "" annots b)
    | item => item) ps assocs
  | .module name (some body) => .module name (some (body.map (Item.decide f)))
  | .pub parent item => .pub parent (Item.decide f item)
  | item => item

/-- What the checker decided is of: the identities of the calls, callables,
fields and tuple patterns it decided something of, and the functions it
decided something in. -/
structure Decided where
  calls : Std.HashSet Nat := {}
  closures : Std.HashSet Nat := {}
  fields : Std.HashSet Nat := {}
  rests : Std.HashSet Nat := {}
  owners : Std.HashSet String := {}

def Decided.of (b : Blocks) : Decided := Id.run do
  let mut d : Decided := {}
  for decision in b.decided do
    d := match decision with
      | .restHere id _ => { d with rests := d.rests.insert id }
      | .letMut owner _ _ _ | .etaHere owner _ _ _ _ => { d with owners := d.owners.insert owner }
      | .refPatsHere id _ => { d with closures := d.closures.insert id }
      | .receiverHere call _ _ | .receiverTemp call _ _ _ | .receiverField call _ _ _ | .receiverCopy call
      | .compareHere call _ => { d with calls := d.calls.insert call }
      | .derefHere id _ | .derefAssignHere id _ | .derefRefHere id _ _ => { d with fields := d.fields.insert id }
      | .eta .. | .refPats .. | .receiver .. => d
  for (call, _) in b.dotChosen do d := { d with calls := d.calls.insert call }
  for ((call, _), _) in b.argsChosen do d := { d with calls := d.calls.insert call }
  pure d

partial def Decided.pat (d : Decided) : Pattern → Bool
  | .var x => (tupleRestOf x).any d.rests.contains
  | .ctor _ _ ps | .tuple ps => ps.any d.pat
  | _ => false

/-- Does a body have something in it the checker decided of? Its nodes are
looked at where they are kept, each kind in its array. -/
def Decided.body (d : Decided) (b : Flat.Body) : Bool :=
  b.exprs.any (fun
    | .call i _ _ | .tailCall i _ _ => d.calls.contains i
    | .closure i _ => d.closures.contains i
    | .fieldOf i _ _ | .refField i _ _ _ _ => d.fields.contains i
    | _ => false)
  || (!d.rests.isEmpty && (b.clauses.any (·.pats.any d.pat)
    || b.stmts.any fun | .let_ p _ => d.pat p | _ => false))

/-- Does an item have something in it the checker decided of? -/
partial def Decided.item (d : Decided) : Syntax.Item → Bool
  | .fn name _ _ _ b => d.owners.contains name || d.body b
  | .impl _ tr head _ _ methods => methods.any fun
    | .fn m _ _ _ b => d.owners.contains (implFnName tr head m) || d.body b
    | item => d.item item
  | .traitInfo _ _ defaults _ _ => defaults.any d.item
  | .module _ (some body) => body.any d.item
  | .pub _ item => d.item item
  | .alias _ b _ => d.body b
  | _ => false

/-- The function of each dot call the checker chose by the value's type,
with the receiver, a variable, given as that one takes it (`0` as it was, `1`
borrowed, `2` borrowed `&mut`), and each argument it chose to give as other
than written: written into the call where it is. -/
def chosenRewrite (b : Blocks) : Flat.FRewrite where
  onExpr go body e :=
    match body.expr e with
    | .call i f args =>
      if !(b.dotChosen.contains i || (List.range args.size).any fun k => b.argsChosen.contains (i, k)) then none
      else some (do
        let args ← args.mapM go.ex
        let (f, args) ← match (← get).expr f, b.dotChosen[i]? with
          | .name _ _, some (fn, how) => do
            let f ← Flat.pushExpr (.name none fn)
            let args ← match how, args.toList with
              | 0, _ => pure args
              | k, a :: rest =>
                match (← get).bare? a with
                | some v => pure (#[← Flat.pushExpr (.ref (k == 2) v)] ++ rest.toArray)
                | none => pure args
              | _, _ => pure args
            pure (f, args)
          | _, _ => do pure (← go.ex f, args)
        let mut out : Array Flat.ExprId := #[]
        for (a, k) in args.toList.zipIdx do
          match b.argsChosen[(i, k)]? with
          | some given => out := out.push (← Flat.flatExpr given)
          | none => out := out.push a
        Flat.pushExpr (.call i f out))
    | _ => none

/-- Each whole number the checker found to be of a scalar type made that
scalar, `u8_of(200)`: Core's types say which whole numbers are what. -/
def scalarLiterals (b : Blocks) (items : List Syntax.Item) : List Syntax.Item := Id.run do
  if b.scalarLits.isEmpty then return items
  let owners : Std.HashSet String := b.scalarLits.fold (fun s (f, _) _ => s.insert f) {}
  items.map fun item => Item.decide (fun name _ body =>
    if !owners.contains name then body else
    let rw : Flat.FRewrite :=
      { onExpr := fun _ body e => (b.scalarLits[(name, body.idOf e)]?).map fun t => do
          -- (A text where `&str` is wanted: its UTF-8 bytes, from the
          -- program's start, borrowed.)
          if t == "%text" then
            let bytes := (String.ofList (((body.textCodes e).getD []).map Char.ofNat)).toUTF8.toList
            let at_ ← Flat.pushExpr (.call 0 (← Flat.pushExpr (.name none "static_bytes"))
              (← bytes.toArray.mapM fun b => Flat.pushExpr (.int b.toNat)))
            return ← Flat.pushExpr (.call 0 (← Flat.pushExpr (.name none "str_at"))
              #[at_, ← Flat.pushExpr (.int bytes.length)])
          let lit ← Flat.pushExpr (body.expr e)
          Flat.pushExpr (.call 0 (← Flat.pushExpr (.name none s!"{t}_of")) #[lit]) }
    rw.body body) item

/-- A program with what the checker decided of it written in: `Decision`s
first (`decideBody`), then the dot calls and arguments it chose, where they
are (`chosenRewrite`). Only the items it
decided something in are written again: what is decided of an item changes
that item alone. -/
def decidedProgram (b : Blocks) (items : List Syntax.Item) : List Syntax.Item := Id.run do
  let d := Decided.of b
  if d.calls.isEmpty && d.closures.isEmpty && d.fields.isEmpty && d.rests.isEmpty && d.owners.isEmpty then
    return scalarLiterals b items
  -- (What the `Decision`s are of, alone.)
  let decisions := Decided.of { b with dotChosen := {}, argsChosen := {} }
  let chosen := !b.dotChosen.isEmpty || !b.argsChosen.isEmpty
  let rw := chosenRewrite b
  -- (The literals the checker found of a type, after the decisions: it
  -- found them in the body read again with those, `x` of a body made
  -- of more than was written.)
  let items := items.map fun item =>
    if !d.item item || !decisions.item item then item else
    b.decided.foldl (fun item dec => Item.decide (fun name _ b => decideBody dec name b) item) item
  let items := scalarLiterals b items
  items.map fun item =>
    if !d.item item then item else
    if chosen then item.mapBodies rw.body else item

end Glorious.Elab
