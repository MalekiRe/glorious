module

public import Glorious.Elab.Base
public import Glorious.Syntax.Resolve
public import Glorious.Addr

/-!
# What is written into a program once it is checked

The constants worked out once the copies for implementations are made
(`Elab.untraitFn`), the fields of a struct split into variables of their
own, and what the checker decided written into the bodies.
-/

public section

namespace Glorious.Elab

open Glorious.Syntax

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
    if fuel == 0 then none
    -- (A type written for a value, or for a function's parameters, says
    -- nothing of its number.)
    if b.mark? fe == some .ascribe || b.mark? fe == some .inst then
      match args[0]? with
      | some a => foldInt fns env (fuel - 1) b a
      | none => none
    else
      let f ← b.bare? fe
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
      | f, inner :: rest =>
        if f.isNone && (b.mark? fe).isNone then none else
        match b.expr inner with
        | .call _ g #[] =>
          match b.bare? g >>= (known[·]?) with
          | some n =>
            if b.mark? fe == some .inst then some (Flat.pushExpr (.int n))
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
    | .impl { trait := tr, head := head, .. } => if tr == .of "Drop" then some head else none
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
    | .impl whole@{ methods := methods, .. } => .impl { whole with methods := (methods.map fun
        | .fn m mps annots ret b => .fn m mps annots ret (split b)
        | item => item) }
    | item => item

/-! ## What the checker decided, written into a flat body -/


/-- A clause whose patterns bind `x` that starts by keeping it in a variable,
written at the place of its first statement (`letMutRewriteF`); a `let x`
the compiler wrote at no place, as of a pattern by reference
(`Flat.byReference`), `let mut x`, and so one at `at_` (a value the front
end named for the statement there, in a block of the statement's own). -/
def heldFirst (x : String) (at_ : Option (Nat × Nat) := none) : Flat.FRewrite where
  onStmts go b ss :=
    match ss with
    | s :: rest =>
      let letOf := fun (s : Flat.StmtId) => match b.stmt s with
        | .let_ (.var y) value => if y == x then some value else none
        | _ => none
      match b.stmt s with
      | .let_ (.var _) _ =>
        (letOf s).map fun value => do pure ((← Flat.pushStmt (.letMut x (← go.ex value))) :: (← go.stmts rest))
      | .located l c inner =>
        if at_ != some (l, c) then none else
        (letOf inner).map fun value => do
          let held ← Flat.pushStmt (.letMut x (← go.ex value))
          pure ((← Flat.pushStmt (.located l c held)) :: (← go.stmts rest))
      | _ => none
    | [] => none
  onClause go b c :=
    let ⟨pats, body⟩ := b.clause c
    let vars := pats.flatMap patVars
    if !vars.contains x then none else some (do
      let body ← go.stmts body.toList
      match body with
      | first :: _ =>
        match (← get).stmt first with
        | .located l c _ =>
          let held ← Flat.pushStmt (.letMut x (← Flat.pushExpr (.name none x)))
          let held ← Flat.pushStmt (.located l c held)
          -- (After those kept so already of names bound before it, so that
          -- they are destroyed in the order Rust's are, the last first.)
          let b ← get
          let before := fun (s : Flat.StmtId) => match b.stmt s with
            | .located _ _ i => match b.stmt i with
              | .letMut y _ => vars.idxOf y < vars.idxOf x
              | _ => false
            | _ => false
          let (kept, rest) := body.span before
          Flat.pushClause ⟨pats, (kept ++ held :: rest).toArray⟩
        | _ => Flat.pushClause ⟨pats, body.toArray⟩
      | [] => Flat.pushClause ⟨pats, #[]⟩)

/-- A value with a `drop` to run that one path uses and another does not is
kept in a variable, as `let mut` keeps it: where it was not used, the variable
destroys it. The checker says which `let`: the `let x` at `line:col` written
`let mut x`; a name a pattern binds kept in a variable straight after, or
where a clause of the statement there that binds it starts. At place `0:0`,
a clause that takes `x` as a parameter (or a name its patterns bind) starts
by keeping it in a variable, written at the place of its first statement,
and a `let x` the compiler wrote at no place is `let mut x` (`heldFirst`). -/
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
        | _ => some (do pure ((← (heldFirst x (some (l, c))).st s) :: (← go.stmts rest)))
      | .let_ (.var y) _ =>
        if line != 0 || col != 0 || y != x then none else (heldFirst x).onStmts go b ss
      | _ => none
    | [] => none
  onClause go b c :=
    if line != 0 || col != 0 then none else (heldFirst x).onClause go b c

/-- A function's body with one thing the checker decided after it read the
body written in: a variable it made a place (`letMut`), a receiver found to
be copied once the bounds were met (`receiverCopy`). What it decided while
reading a body it wrote there itself (`Blocks.bodies`). `name` is the name
the function is checked by. -/
def decideBody (d : Decision) (name : String) (b : Flat.Body) : Flat.Body :=
  match d with
  | .letMut owner line col x => if name == owner then (letMutRewriteF line col x).body b else b
  | .receiverCopy call => (receiverCopyNode call b).getD b
  | _ => b

/-- Every function of an item with what the checker decided written in, each
under the name it is checked by. -/
partial def Item.decide (f : String → List (Option TypeExpr) → Flat.Body → Flat.Body) : Syntax.Item → Syntax.Item
  | .fn name ps annots ret b => .fn name ps annots ret (f name annots b)
  | .impl whole@{ trait := tr, head := head, methods := methods, .. } => .impl { whole with methods := (methods.map fun
    | .fn m mps annots ret b => .fn m mps annots ret (f (implFnName tr.spelled head m) annots b)
    | item => Item.decide f item) }
  | .traitInfo n supers defaults ps assocs => .traitInfo n supers (defaults.map fun
    | .fn m mps annots ret b => .fn m mps annots ret (f "" annots b)
    | item => item) ps assocs
  | .module name (some body) => .module name (some (body.map (Item.decide f)))
  | .pub parent item => .pub parent (Item.decide f item)
  | item => item

/-- The calls the checker chose the function or an argument of
(`chosenRewrite`). -/
def chosenCalls (b : Blocks) : Std.HashSet Nat :=
  b.argsChosen.fold (fun s (call, _) _ => s.insert call) (b.dotChosen.fold (fun s call _ => s.insert call) {})

/-- Does an item have a call in it of `calls`? -/
partial def hasCall (calls : Std.HashSet Nat) : Syntax.Item → Bool
  | .fn _ _ _ _ b | .alias _ b _ => b.exprs.any fun
    | .call i _ _ | .tailCall i _ _ => calls.contains i
    | _ => false
  | .impl { methods := methods, .. } => methods.any (hasCall calls)
  | .traitInfo _ _ defaults _ _ => defaults.any (hasCall calls)
  | .module _ (some body) => body.any (hasCall calls)
  | .pub _ item => hasCall calls item
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

/-- A program as the checker read it: each function's body the checker's
(`Blocks.bodies`), with what it found written where it found it; then the
literals it found of a type (`scalarLiterals`), and the dot calls and
arguments it chose, where they are (`chosenRewrite`). -/
def decidedProgram (b : Blocks) (items : List Syntax.Item) : List Syntax.Item :=
  let items := items.map (Item.decide fun name _ body => (b.bodies[name]?).getD body)
  let items := scalarLiterals b items
  let calls := chosenCalls b
  if calls.isEmpty then items else
  let rw := chosenRewrite b
  items.map fun item => if hasCall calls item then item.mapBodies rw.body else item

end Glorious.Elab
