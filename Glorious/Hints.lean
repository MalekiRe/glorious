module

public import Glorious.Typer

/-!
# Core's types from the checker's, forward

Each function at a signature gone through once, each local's type found
from its parts' and, for what its parts do not say, from the type the
checker found of the expression it is made for (`Blocks.nodeTys`, by the
node's identity; the elaborator notes which local is made for which,
`Output.fnNodes`). Nothing is unified.

For now beside `Typer`: each hint `Typer` found is compared with the one
found here (`GLORIOUS_TRACE=hints`), and `Typer`'s is what the walk goes on
with.
-/

@[expose] public section

namespace Glorious.Hints

open Lower Core Syntax

structure Env where
  decls : Typer.Decls
  p : Program
  /-- The checker's type of the expression each local is made for, by
  function, clause and local, where it knows the type whole. -/
  said : Std.HashMap (Nat × Nat × Nat) TypeExpr := {}
  names : Array String := #[]
  /-- Each top-level function's type as the checker found it. -/
  selfTy : Std.HashMap Nat TypeExpr := {}
  /-- Each implementation's function's `Self`, of the implementation's type
  parameters. -/
  implSelf : Std.HashMap Nat TypeExpr := {}
  /-- What each type parameter of the function a local is a closure of is,
  where the local is made for a call of it, as the checker found it there:
  by function, clause and local. -/
  insts : Std.HashMap (Nat × Nat × Nat) (List (String × Option TypeExpr)) := {}
  /-- The functions of a top-level function that is general in nothing
  (`%settled`). -/
  settled : Std.HashSet Nat := {}

/-- How the hints found compare, by what they are of. -/
structure Tally where
  counts : Std.HashMap String (Nat × Nat × Nat) := {}
  /-- What a function's type parameters are where a closure of each callable
  was made, learned there: where its body is gone through, they are. -/
  closureBinds : Std.HashMap (Nat × List Ty) (List (String × Ty)) := {}
  calledBinds : Std.HashMap (Nat × List Ty) (List (String × Ty)) := {}
  lost : Nat := 0
  examples : Array String := #[]

def Tally.add (t : Tally) (kind : String) (r : Option Bool) (ex : Option String := none) : Tally :=
  let (a, d, u) := t.counts.getD kind (0, 0, 0)
  let c := match r with
    | some true => (a + 1, d, u)
    | some false => (a, d + 1, u)
    | none => (a, d, u + 1)
  { t with counts := t.counts.insert kind c
           examples := match ex with
             | some e => if t.examples.size < 60 then t.examples.push e else t.examples
             | none => t.examples }

/-- What a type counting a length (`B0<B1<Z>>`) counts. -/
partial def countTy (d : Typer.Decls) : Ty → Option Nat
  | .data id args =>
    let name := (d.typeNames[id]?).getD ""
    match args with
    | [] => if name == "Z" || name.endsWith "::Z" then some 0 else none
    | [inner] =>
      if name.endsWith "B0" then (countTy d inner).map (2 * ·)
      else if name.endsWith "B1" then (countTy d inner).map (2 * · + 1)
      else none
    | _ => none
  | _ => none

/-- A type written whole, as Core's types are: a callable's not (its
effects and what it was made with are not written). -/
partial def tyOf (d : Typer.Decls) (vars : List (String × Ty) := []) : TypeExpr → Option Ty
  | .name x args =>
    if let (some t, []) := (vars.lookup x, args) then some t
    -- (What nothing decided in a function general in nothing, the program
    -- checked whole, as `Typer` has it: `()`; `%settled` says it is such a
    -- one.)
    else if x.startsWith "%rigid:%" && args.isEmpty && (vars.lookup "%settled").isSome then some .unit
    -- (A callable for every lifetime, `%for<'a, fn(..)>`: the callable.)
    else if x == rankedMark then args.getLast?.bind (tyOf d vars)
    -- (What an `is` found, `%is:a,b<A, B>`: the values, a tuple.)
    else if (packNames x).isSome then do pure (.tuple (← args.mapM (tyOf d vars)))
    else if x.startsWith "'" then some (.ref .unit)
    else if x == "Int" then some .int
    else if isScalar x then some (.scalar (scalarBits x))
    else if x == "Fixed" then
      match args with
      | [t, n] => do
        -- (A length that is a parameter: as it is, a length or the type
        -- that counts it.)
        let len ← match n with
          | .name p [] => match vars.lookup p with
            | some (.data id args) =>
              if id ≥ lenBase then some (.data id args)
              else (countTy d (.data id args)).map fun k => .data (lenBase + k) []
            | some _ => none
            | none => lengthOf n
          | _ => lengthOf n
        pure (.data fixedName [← tyOf d vars t, len])
      | _ => none
else match d.typeIds[x]? with
      | some id => do
        let lifetimes := ((d.typeParams[id]?).getD []).map (·.startsWith "'")
        -- (A lifetime given is a reference to nothing, whatever it is.)
        let given ← if args.length == lifetimes.length then
            (args.zip lifetimes).mapM fun (a, l) => if l then some (.ref .unit) else tyOf d vars a
          else args.mapM (tyOf d vars)
        let mut missing := lifetimes.length - given.length
        let mut rest := given
        let mut out : Array Ty := #[]
        for isLife in lifetimes do
          if isLife && missing > 0 then
            out := out.push (.ref .unit)
            missing := missing - 1
          else
            match rest with
            | a :: more =>
              out := out.push a
              rest := more
            | [] => none
        pure (.data id (out.toList ++ rest))
      | none => none
  | .tuple ts => do pure (.tuple (← ts.mapM (tyOf d vars)))
  | .ref _ t _ => do pure (.ref (← tyOf d vars t))
  | .performs r _ => tyOf d vars r
  | .never => some .never
  -- (What it performs, each operation of each effect at the effect's
  -- arguments; what it was made with is not written, found apart.)
  | .fn ps (.performs r effs) => do
    let eff ← effs.flatMapM fun (e, args) => do
      let targs ← args.mapM (tyOf d vars)
      pure (((d.effectOps[e]?).getD []).map (·, targs))
    pure (.fn (← spread ps) (← tyOf d vars r) eff false none)
  | .fn ps r => do pure (.fn (← spread ps) (← tyOf d vars r) [] false none)
  | _ => none
where
  /-- A callable's parameters, `%Spread<P>` those of the tuple `P` is. -/
  spread (ps : List TypeExpr) : Option (List Ty) :=
    ps.flatMapM fun p => match p with
      | .name x [a] => if x == spreadParams then match tyOf d vars a with
          | some (.tuple ts) => some ts
          | _ => none
        else (tyOf d vars p).map ([·])
      | _ => (tyOf d vars p).map ([·])
  lengthOf (n : TypeExpr) : Option Ty :=
    let rec count : TypeExpr → Option Nat
      | .name "Z" [] | .name "%prelude::Z" [] => some 0
      | .name b [inner] =>
        if b.endsWith "B0" then (count inner).map (2 * ·)
        else if b.endsWith "B1" then (count inner).map (2 * · + 1)
        else none
      | _ => none
    (count n).map fun k => .data (lenBase + k) []

/-- The same, but for what callables perform and were made with, which are
found apart. -/
partial def shape : Ty → Ty
  | .fn ps r _ _ _ => .fn (ps.map shape) (shape r) [] false none
  | .tuple fs => .tuple (fs.map shape)
  | .data n args => .data n (args.map shape)
  | .ref t => .ref (shape t)
  | t => t

/-- What each type parameter (`%rigid:T`) a written type names is, where
the type is `t`: added to `binds`; where the two are not alike, nothing
(none is learned of a type that does not fit what is written). -/
partial def matchTyOpt (d : Typer.Decls) (binds : List (String × Ty)) : TypeExpr → Ty → Option (List (String × Ty))
  | .name x [], t =>
    if x.startsWith "%rigid:" then
      match binds.lookup x with
      | some u => if shape u == shape t then some binds else none
      | none => some ((x, t) :: binds)
    else match tyOf d [] (.name x []) with
      | some u => if shape u == shape t then some binds else none
      | none => some binds
  | .name x args, t =>
    if x == rankedMark then match args.getLast? with
      | some a => matchTyOpt d binds a t
      | none => some binds
    else match t with
    | .data n targs =>
      if d.typeIds[x]? == some n then
        let lifetimes := ((d.typeParams[n]?).getD []).map (·.startsWith "'")
        let typed := (lifetimes.zip targs).filterMap fun (l, t) => if l then none else some t
        if typed.length == args.length then
          (args.zip typed).foldlM (fun b (a, t) => matchTyOpt d b a t) binds
        else some binds
      else if x == "Fixed" && n == fixedName then
        match args, targs with
        | a :: _, t :: _ => matchTyOpt d binds a t
        | _, _ => some binds
      else none
    | .int => if x == "Int" then some binds else none
    | .scalar _ => if isScalar x then some binds else none
    | _ => none
  | .tuple ps, .tuple ts =>
    if ps.length == ts.length then (ps.zip ts).foldlM (fun b (a, t) => matchTyOpt d b a t) binds else none
  | .tuple _, _ => none
  | .ref _ a _, .ref t => matchTyOpt d binds a t
  | .ref _ _ _, _ => none
  | .fn ps r, .fn ts s _ _ _ =>
    if ps.length == ts.length then do
      let b ← (ps.zip ts).foldlM (fun b (a, t) => matchTyOpt d b a t) binds
      matchTyOpt d b r s
    else none
  | .fn _ _, _ => none
  | .performs r _, t => matchTyOpt d binds r t
  | _, _ => some binds

/-- `matchTyOpt`, `binds` as they were where the two are not alike. -/
def matchTy (d : Typer.Decls) (binds : List (String × Ty)) (te : TypeExpr) (t : Ty) : List (String × Ty) :=
  (matchTyOpt d binds te t).getD binds

/-- A field of a value of a type, where the type says it. -/
def fieldOf (d : Typer.Decls) (t : Ty) (i : Nat) : Option Ty :=
  match t with
  | .tuple fs => fs[i]?
  | .data n args =>
    if n == fixedName then args.head?
    else match d.tagsOf[n]? with
      | some [tag] => do
        let (_, fields) ← d.ctors[tag]?
        let f ← fields[i]?
        tyOf d (((d.typeParams[n]?).getD []).zip args) f
      | _ => none
  | _ => none

/-- Is `mine` what `theirs` is, but where `theirs` leaves it undecided
(`anyName`, Typer's)? -/
partial def fits (mine theirs : Ty) : Bool :=
  match mine, theirs with
  | _, .data n [] => n == anyName || mine == theirs
  -- (What Typer decided nothing of it makes `()`.)
  | _, .tuple [] => true
  | .tuple as, .tuple bs => as.length == bs.length && (as.zip bs).all fun (a, b) => fits a b
  | .data n as, .data m bs => n == m && as.length == bs.length && (as.zip bs).all fun (a, b) => fits a b
  | .ref a, .ref b => fits a b
  | .fn ps r _ _ _, .fn qs s _ _ _ => ps.length == qs.length && fits r s && (ps.zip qs).all fun (a, b) => fits a b
  | a, b => a == b

/-- Where two types first differ, each there (`GLORIOUS_TRACE=hints`). -/
partial def diffAt (a b : Ty) : Option (Ty × Ty) :=
  if fits a b then none else
  match a, b with
  | .tuple as, .tuple bs => if as.length != bs.length then some (a, b) else (as.zip bs).findSome? fun (x, y) => diffAt x y
  | .data n as, .data m bs => if n != m || as.length != bs.length then some (a, b) else (as.zip bs).findSome? fun (x, y) => diffAt x y
  | .ref x, .ref y => diffAt x y
  | .fn ps r _ _ _, .fn qs s _ _ _ =>
    if ps.length != qs.length then some (a, b)
    else ((ps.zip qs).findSome? fun (x, y) => diffAt x y) <|> diffAt r s
  | _, _ => some (a, b)

/-- The value a callable gives, of its type. -/
def retOf : Ty → Option Ty
  | .fn _ r _ _ _ => some r
  | _ => none

/-- A written type with the type parameters `ps` named as the checker's
(`%rigid:T`). -/
partial def rigidOf (ps : List String) : TypeExpr → TypeExpr
  | .name x [] => if ps.contains x then .name s!"%rigid:{x}" [] else .name x []
  | .name x args => .name x (args.map (rigidOf ps))
  | .tuple ts => .tuple (ts.map (rigidOf ps))
  | .fn as r => .fn (as.map (rigidOf ps)) (rigidOf ps r)
  | .performs r effs => .performs (rigidOf ps r) effs
  | .ref u t l => .ref u (rigidOf ps t) l
  | t => t

/-- The type of what a memory operation gives. -/
def memTy (env : Env) (Γ : Array (Option Ty)) (op : MemOp) (args : List Atom) : Option Ty :=
  let atomTy := fun (a : Atom) => match a with
    | .var i => Γ[i]?.join
    | .int _ => some .int
  match op, args with
  | .load, [r] => match atomTy r with | some (.ref t) => some t | _ => none
  | .store, _ | .free, _ | .writeBits, _ | .copy, _ => some .unit
  | .swap, [_, v] => atomTy v
  | .tag, _ | .readBits, _ => some .int
  | .alloc, _ | .sizeOf, _ | .alignOf, _ | .staticAt, _ => some (.scalar (-64))
  | .focus, [r, .int i] => match atomTy r with
    | some (.ref t) => (fieldOf env.decls t i.toNat).map .ref
    | _ => none
  -- (An element of a `[T; N]` at a place.)
  | .focus, [r, _, .int (-1)] => match atomTy r with
    | some (.ref t) => (fixedElem t).map .ref
    | _ => none
  -- (A field of a constructor of several, the one that built it said.)
  | .focus, [r, .int i, .int built] => match atomTy r with
    | some (.ref (.data n args)) => do
      let (_, fields) ← env.decls.ctors[built.toNat]?
      let f ← fields[i.toNat]?
      (tyOf env.decls (((env.decls.typeParams[n]?).getD []).zip args) f).map .ref
    | _ => none
  | .deref, [_, _, .int tag] => do
    let (owner, _) ← env.decls.ctors[tag.toNat]?
    match atomTy (args.headD (.int 0)) with
    | some (.data n (t :: _)) => if n == owner then some (.ref t) else none
    | _ => none
  | .addressOf, [r, .int _] => match atomTy r with
    | some (.ref (.data _ (_ :: _))) => none
    | _ => none
  | _, _ => none

/-- The type of what a host operation gives: of what it is given, or, of
one that gives what the program sees as another type (14), as the checker
says it (`said`). -/
def hostTy (id : Nat) (args : List Atom) (atomTy : Atom → Option Ty) (said : Option Ty) : Option Ty :=
  match id, args with
  | 0, _ | 8, _ | 21, _ | 22, _ => some .unit
  | 1, _ | 10, _ => some (.tuple [.int, .int])
  | 2, _ | 6, _ => some .int
  | 5, _ => some (.scalar (-64))
  | 7, [_, of] => (atomTy of).bind fixedElem
  | 9, [v, _] => (atomTy v).map fun t => .tuple [.int, t]
  | 14, _ => said
  | _, _ => none

mutual
/-- The types a pattern binds of a value of a type, the declarations read. -/
partial def patTysD (d : Typer.Decls) : Pat → Ty → Option (List Ty)
  | .wild, _ => some []
  | .bind, τ => some [τ]
  | .int _, _ => some []
  | .ctor 0 ps, .tuple fs => patsTysD d ps fs
  | .ctor tag ps, .data n args =>
    if n == fixedName then match args with
      | [t, _] => patsTysD d ps (List.replicate ps.length t)
      | _ => none
    else do
    let (_, fields) ← d.ctors[tag]?
    let vars := ((d.typeParams[n]?).getD []).zip args
    patsTysD d ps (← fields.mapM (tyOf d vars))
  | _, _ => none
partial def patsTysD (d : Typer.Decls) : List Pat → List Ty → Option (List Ty)
  | [], [] => some []
  | p :: ps, τ :: τs => do pure ((← patTysD d p τ) ++ (← patsTysD d ps τs))
  | _, _ => none
end

/-- What a constructor builds, its type's arguments read off what its
fields are given (`[T; N]`'s too); one no field shows, of what the checker
said of it. -/
def constructOf (env : Env) (Γ : Array (Option Ty)) (binds : List (String × Ty)) (said : Option TypeExpr)
    (tag : Nat) (args : List Atom) : Option Ty := do
  let atomTy := fun (a : Atom) => match a with
    | .var i => Γ[i]?.join
    | .int _ => some .int
  if fixedBase ≤ tag then
    let n := tag - fixedBase
    let elem ← match args.head? with
      | some a => atomTy a
      | none => (said.bind (tyOf env.decls binds)).bind fixedElem
    return .data fixedName [elem, .data (lenBase + n) []]
  let (owner, fields) ← env.decls.ctors[tag]?
  let params := (env.decls.typeParams[owner]?).getD []
  let tys ← args.mapM atomTy
  let learned := (fields.zip tys).foldl (fun b (f, t) => matchTy env.decls b (rigidOf params f) t) []
  let saidArgs : List (Option TypeExpr) := match said with
    | some (.name _ as) => if as.length == params.length then as.map some else params.map fun _ => none
    | _ => params.map fun _ => none
  let targs ← (params.zip saidArgs).mapM fun (p, s) =>
    if p.startsWith "'" then some (.ref .unit)
    else (learned.lookup s!"%rigid:{p}").orElse fun _ => s.bind (tyOf env.decls binds)
  pure (.data owner targs)

/-- The type of a right-hand side, where its parts or the checker say it. -/
def rhsTy (env : Env) (binds : List (String × Ty)) (Γ : Array (Option Ty)) (said : Option TypeExpr) : Rhs → Option Ty
  | .atom a => atomTy Γ a
  | .prim p args =>
    match p, args with
    | .cast b into, _ => some (if into then .scalar b else .int)
    | .fixed 0, [a, .int n] => do pure (.data fixedName [← atomTy Γ a, .data (lenBase + n.toNat) []])
    | .fixed 2, a :: _ => do fixedElem (← atomTy Γ a)
    | .fixed 3, a :: _ => atomTy Γ a
    | .fixed 4, _ => some .int
    | .fixed _, _ => none
    | _, _ => some .int
  | .construct 0 args => do pure (.tuple (← args.mapM (atomTy Γ)))
  | .construct tag args =>
    (said.bind (tyOf env.decls binds)).orElse fun _ => constructOf env Γ binds said tag args
  | .place pl => do
    let mut t ← Γ[pl.var]?.join
    for i in pl.path do t ← fieldOf env.decls t i
    pure t
  | .closure _ caps => do
    match ← said.bind (tyOf env.decls binds) with
    | .fn ps r eff _ _ => pure (.fn ps r eff false (some (← caps.mapM (atomTy Γ))))
    | _ => none
where
  atomTy (Γ : Array (Option Ty)) : Atom → Option Ty
    | .var i => Γ[i]?.join
    | .int _ => some .int

/-- How the local `i` is first used in `tm` (`GLORIOUS_TRACE=hints`). -/
partial def firstRef (i : Nat) (tm : Tm) : String :=
  let is := fun (a : Atom) => a == .var i
  let some_ := fun (as : List Atom) => as.any is
  match tm with
  | .ret a => if is a then "returned" else "unused"
  | .let_ rhs b => match rhs with
    | .atom a => if is a then "copied" else firstRef i b
    | .construct _ as => if some_ as then "stored" else firstRef i b
    | .closure _ as => if some_ as then "captured" else firstRef i b
    | .prim _ as => if some_ as then "prim" else firstRef i b
    | .place pl => if pl.var == i then "place" else firstRef i b
  | .call h as b => if is h then "called" else if some_ as then "given" else firstRef i b
  | .tail h as => if is h then "called" else if some_ as then "given to a tail call" else "unused"
  | .mem _ as b => if some_ as then "memory" else firstRef i b
  | .host _ as b => if some_ as then "host" else firstRef i b
  | .handle _ _ cs t b => if is t then "handled" else if some_ cs then "handler captures" else firstRef i b
  | .handleTail _ _ cs t => if is t then "handled" else if some_ cs then "handler captures" else "unused"
  | .perform _ as b => if some_ as then "performed with" else firstRef i b
  | .raise _ as => if some_ as then "raised with" else "unused"
  | .label t b => if is t then "label" else firstRef i b
  | .labelTail t => if is t then "label" else "unused"
  | .guard c t b => if is c || is t then "guard" else firstRef i b
  | .guardTail c t => if is c || is t then "guard" else "unused"
  | .cancel k b => if is k then "cancelled" else firstRef i b
  | .cell a t b | .cellL _ a t b => if is a then "cell init" else if is t then "cell" else firstRef i b
  | .cellTail a t | .cellTailL _ a t => if is a then "cell init" else if is t then "cell" else "unused"
  | .lend _ r t pre post b => if is r || is t || some_ pre || some_ post then "lend" else firstRef i b

/-- A clause being gone through: each local's type found so far, the
closures whose type waits on where they are used (by local: the function
and what it was made with), the hints found in order (none where not, or
not yet: by local, which), and the type parameters learned. -/
structure W where
  Γ : Array (Option Ty) := #[]
  pend : Std.HashMap Nat (Nat × List Ty) := {}
  hints : Array (Option Hint) := #[]
  hintAt : Std.HashMap Nat Nat := {}
  binds : List (String × Ty) := []
  /-- The type parameters where a closure of each callable of the function's
  own was made (by the callable and what it was made with). -/
  made : Array ((Nat × List Ty) × List (String × Ty)) := #[]
  /-- What each type parameter of a function called is, at the signature it
  is called at (by the function and what it is given). -/
  called : Array ((Nat × List Ty) × List (String × Ty)) := #[]
  /-- Why a local's type was not found, by local (`GLORIOUS_TRACE=hints`). -/
  why : Std.HashMap Nat String := {}
  /-- What the clause gives, where that is known: what a scope it ends in
  that does not return gives. -/
  ret : Option Ty := none
  /-- What the function performs: what a callable it makes and the checker
  says nothing of performs too, as `Typer`'s one row for the code around. -/
  eff : Row := []
  /-- Each function at each signature a closure of it is made at. -/
  uses : Array (Nat × FnSig) := #[]
  /-- The functions whose bodies are being gone through to find what they
  give (`fnRet`): one that is reached again does not return there. -/
  stack : List Nat := []

def W.atomTy (w : W) : Atom → Option Ty
  | .var i => w.Γ[i]?.join
  | .int _ => some .int

/-- The local `i`'s type found: where it waited, its hint too. -/
def W.found (w : W) (i : Nat) (σ : Ty) : W :=
  let w := { w with Γ := w.Γ.set! i (some σ), pend := w.pend.erase i }
  match w.hintAt[i]? with
  | some h => { w with hints := w.hints.set! h (some (.ty σ)) }
  | none => w

/-- What each type parameter of `g` is where the local `i` is a closure of
it given `params`, as the checker found it at the call (`Env.insts`). -/
def W.noteCalled (w : W) (env : Env) (f c i g : Nat) (params : List Ty) : W :=
  match env.insts[(f, c, i)]? with
  | some ps =>
    let binds := ps.flatMap fun (p, te) =>
      match te.bind (tyOf env.decls w.binds) with
      | none => []
      | some t =>
        -- (`Self` at a call of a trait's function: the implementation's
        -- type parameters, of its `Self`.)
        if p == "%Self" then match env.implSelf[g]? with
          | some self => matchTy env.decls [] self t
          | none => []
        else [(s!"%rigid:{p}", t)]
    if binds.isEmpty then w else { w with called := w.called.push ((g, params), binds) }
  | none => w

/-- A local and its hint. -/
def W.bind (w : W) (σ : Option Ty) (hinted : Bool) : W :=
  let i := w.Γ.size
  let w := { w with Γ := w.Γ.push σ }
  if hinted then { w with hints := w.hints.push (σ.map .ty), hintAt := w.hintAt.insert i w.hints.size }
  else w

/-- A handler's functions at their signatures: its completion given what
the handled computation gives, each arm what its operation takes and the
resumption, all made with the handler's captures, giving what the handler
gives, performing what the code around does. -/
def handlerUses (env : Env) (w : W) (ret : Nat) (ops : List (Nat × Nat)) (caps : List Ty) (σ ρ : Ty) (H : Row) : W := Id.run do
  let mut w := { w with uses := w.uses.push (ret, { caps, params := [σ], ret := ρ, eff := w.eff }) }
  for (op, arm) in ops do
    let some (ps, payload, result) := env.decls.ops[op]? | continue
    let some targs := H.lookup op | continue
    let vars := ps.zip targs
    let some payload := payload.mapM (tyOf env.decls vars) | continue
    let params ← match result with
      | some r => match tyOf env.decls vars r with
        | some o => pure (payload ++ [.fn [o] ρ w.eff true none])
        | none => continue
      | none => pure payload
    w := { w with uses := w.uses.push (arm, { caps, params, ret := ρ, eff := w.eff }) }
  pure w

mutual

/-- The type of a closure that waited, at its first use as a callable, `at_`
(`pend`): what it is given read off that; what it gives what the place says
it gives where the checker says that, else what the function says it
gives, else its body's. -/
partial def useOf (env : Env) (depth : Nat) (f c : Nat) (w : W) (at_ : Tm) : W := Id.run do
  let callee := fun (a : Atom) => match a with
    | .var i => (w.pend[i]?).map (i, ·)
    | .int _ => none
  let mut w := w
  -- (A closure given to a callable of a known type: of the type it takes
  -- there, what it was made with its own.)
  match at_ with
  | .call h args _ | .tail h args =>
    if let some (.fn ps _ _ _ _) := w.atomTy h then
      for (a, p) in args.zip ps do
        if let some (i, (g, caps)) := callee a then
          if let .fn qs r eff once _ := p then
            w := w.found i (.fn qs r eff once (some caps))
            w := { w with uses := w.uses.push (g, { caps, params := qs, ret := r, eff })
                          why := w.why.insert i "given where its type is known" }
  | _ => pure ()
  -- (The callable, what it is given, and the local the use binds, if any.)
  let uses : List (Atom × Option (List Ty)) := match at_ with
    | .guard cl t _ | .guardTail cl t => [(cl, some []), (t, some [])]
    | .cell a t _ | .cellTail a t => [(t, (w.atomTy a).map fun σ => [.ref σ])]
    | .lend _ r t pre post _ => [(t, do pure ((← pre.mapM w.atomTy) ++ [← w.atomTy r] ++ (← post.mapM w.atomTy)))]
    | .call h args _ | .tail h args => [(h, args.mapM w.atomTy)]
    | .handle _ _ _ t _ | .handleTail _ _ _ t => [(t, some [])]
    | .label t _ | .labelTail t =>
      -- (Given the label, whose result is the scope's: as the checker says
      -- it, else as the scope's body gives it, `labelRet`.)
      [(t, do
        let σ ← ((env.said[(f, c, w.Γ.size)]?).bind (tyOf env.decls w.binds)).orElse fun _ =>
          match t with
          | .var i => do
            let (g, caps) ← w.pend[i]?
            labelRet env depth g w.binds caps
          | _ => none
        pure [.fn [σ] .never [] false none])]
    | _ => []
  for (a, params) in uses do
    let some (i, (g, caps)) := callee a | continue
    let some params := params | continue
    -- (What the use gives, as the checker says it: a call's.)
    let atUse := match at_ with
      | .call .. => (env.said[(f, c, w.Γ.size)]?).bind (tyOf env.decls w.binds)
      | _ => none
    let written : Option Ty := (do
      let (tparams, annots, ret) ← env.decls.fns[g]?
      -- (One that says nothing of it gives `()`.)
      let ret := ret.getD (.tuple [])
      let b := (annots.zip params).foldl (fun b (a, p) => match a with
        | some te => matchTy env.decls b (rigidOf tparams te) p
        | none => b) []
      tyOf env.decls b (rigidOf tparams ret)).orElse fun _ => do
      -- (Or what the checker found it to give, of what it is given.)
      let .fn ps r ← env.selfTy[g]? | none
      let b := (ps.zip params).foldl (fun b (a, p) => matchTy env.decls b a p) []
      tyOf env.decls b r
    -- (One that does not return gives what its place wants: the clause's
    -- result where it ends the clause, else as the checker says it.)
    let wanted := match at_ with
      | .tail .. | .guardTail .. | .cellTail .. | .cellTailL .. | .labelTail _ | .handleTail .. => w.ret
      | _ => (env.said[(f, c, w.Γ.size)]?).bind (tyOf env.decls w.binds)
    -- (A function that says nothing of what it gives and does not return
    -- gives what its place wants, not `()`.)
    let ret := atUse <|> (match fnRet env (depth + 1) g w.binds params caps w.stack with
      | some .never => wanted <|> some .never
      | none => written <|> wanted
      | r => r)
    if let some r := ret then
      let σ : Ty := .fn params r w.eff false (some caps)
      w := w.found i σ
      w := w.noteCalled env f c i g params
      w := { w with uses := w.uses.push (g, { caps, params, ret := r, eff := w.eff })
                    why := w.why.insert i s!"used at {firstRef i at_}, given {params.map Typer.showTy}, gives by {if atUse.isSome then "the use" else "its body or its place"}" }
      -- (What the checker said of it, a type parameter it names learned of
      -- what it was found to be.)
      if let some te := env.said[(f, c, i)]? then
        w := { w with binds := matchTy env.decls w.binds te σ }
  pure w

/-- Go through a clause: its hints and what it gives. -/
partial def go (env : Env) (depth : Nat) (f c : Nat) (w : W) (tm : Tm) : W × Option Ty :=
  let said := fun (i : Nat) => env.said[(f, c, i)]?
  let w := if w.pend.isEmpty then w else useOf env depth f c w tm
  match tm with
  | .ret a => (w, w.atomTy a)
  | .tail g _ => (w, (w.atomTy g).bind retOf)
  | .raise .. => (w, some .never)
  | .labelTail thunk | .guardTail _ thunk | .cellTail _ thunk | .cellTailL _ _ thunk => (w, (w.atomTy thunk).bind retOf)
  | .handleTail ret ops caps thunk =>
    let w := match caps.mapM w.atomTy with
      | some capTys => if w.binds.isEmpty then w else
          { w with made := (ret :: ops.map (fun (p : Nat × Nat) => p.2)).foldl (fun (m : Array ((Nat × List Ty) × List (String × Ty))) g => m.push ((g, capTys), w.binds)) w.made }
      | none => w
    let H : Option Row := ops.mapM fun (op, _) => do
      let (ps, _, _) ← env.decls.ops[op]?
      if ps.isEmpty then pure (op, []) else
        match w.atomTy thunk with
        | some (.fn _ _ eff _ _) => (eff.lookup op).map (op, ·)
        | _ => none
    -- (What it gives is what the clause gives: found by its callers.)
    let w := { w with hints := w.hints.push (H.map (.handler (w.ret.getD .never) ·)) }
    let w := match w.ret, H, caps.mapM w.atomTy, (w.atomTy thunk).bind retOf with
      | some ρ, some H, some capTys, some σ => handlerUses env w ret ops capTys σ ρ H
      | _, _, _, _ => w
    (w, none)
  | .let_ rhs body =>
    let i := w.Γ.size
    let mine := rhsTy env w.binds w.Γ (said i) rhs
    let w := if mine.isSome then w else { w with why := w.why.insert i (match rhs with
      | .place pl => match w.Γ[pl.var]?.join with
        | none => "place of unknown"
        | some t => s!"place of {match t with | .data .. => "data" | .ref _ => "ref" | .tuple _ => "tuple" | _ => "other"}"
      | .construct _ _ => match said i with
        | some te => s!"construct said, not written: {(te.spell.take 80).toString} with {w.binds.map (·.1)}"
        | none => "construct not said"
      | .closure _ caps => if (caps.mapM w.atomTy).isNone then "closure caps unknown" else match said i with
        | some te => s!"closure said, not written: {(te.spell.take 120).toString} with {w.binds.map (·.1)}"
        | none => s!"closure waits: {firstRef i body} (with {w.binds.map (·.1)}, the use's said {((said (i + 1)).map fun te => (te.spell.take 80).toString).getD "none"})"
      | .atom _ => "atom of unknown"
      | .prim _ _ => "prim"
      ) }
    let w := match said i, mine with
      | some te, some m => { w with binds := matchTy env.decls w.binds te m }
      | _, _ => w
    match rhs, mine with
    | .closure g caps, none =>
      let w := w.bind none true
      match caps.mapM w.atomTy with
      | some capTys =>
        let w := { w with pend := w.pend.insert i (g, capTys) }
        -- (One of no parameters: given nothing, whatever it is used as;
        -- what it gives its body's, found now where the body says.)
        let w := match env.p.fns[g]? with
          | some fn =>
            if fn.clauses.all (·.pats.isEmpty) && !fn.clauses.isEmpty then
              match fnRet env (depth + 1) g w.binds [] capTys w.stack with
              | some .never | none => w
              | some r =>
                let w := w.found i (.fn [] r w.eff false (some capTys))
                { w with uses := w.uses.push (g, { caps := capTys, params := [], ret := r, eff := w.eff }) }
            else w
          | none => w
        let w := if w.binds.isEmpty || (env.selfTy[g]?).isSome || (env.decls.fns[g]?).isSome then w
          else { w with made := w.made.push ((g, capTys), w.binds) }
        go env depth f c w body
      | none => go env depth f c w body
    | .closure g caps, some σ =>
      let w := w.bind (some σ) true
      let w := match σ with
        | .fn ps r eff _ (some capTys) =>
          let w := w.noteCalled env f c i g ps
          { w with uses := w.uses.push (g, { caps := capTys, params := ps, ret := r, eff }) }
        | _ => w
      let w := match caps.mapM w.atomTy with
        | some capTys =>
          if w.binds.isEmpty || (env.selfTy[g]?).isSome || (env.decls.fns[g]?).isSome then w
          else { w with made := w.made.push ((g, capTys), w.binds) }
        | none => w
      go env depth f c w body
    | _, _ => go env depth f c (w.bind mine true) body
  | .call g _ body =>
    match (w.atomTy g).bind retOf with
    | some .never => go env depth f c (w.bind ((said w.Γ.size).bind (tyOf env.decls w.binds)) true) body
    | r => go env depth f c (w.bind r false) body
  | .handle ret ops caps thunk body =>
    -- (Its functions are of this one's type parameters.)
    let w := match caps.mapM w.atomTy with
      | some capTys => if w.binds.isEmpty then w else
          { w with made := (ret :: ops.map (fun (p : Nat × Nat) => p.2)).foldl (fun (m : Array ((Nat × List Ty) × List (String × Ty))) g => m.push ((g, capTys), w.binds)) w.made }
      | none => w
    -- (What it gives, as the checker says it; the operations it serves,
    -- each at its effect's arguments: none, of an effect that takes none.)
    let ρ := (said w.Γ.size).bind (tyOf env.decls w.binds)
    let H : Option Row := ops.mapM fun (op, _) => do
      let (ps, _, _) ← env.decls.ops[op]?
      if ps.isEmpty then pure (op, []) else
        -- (Else at what the handled computation performs it at.)
        match w.atomTy thunk with
        | some (.fn _ _ eff _ _) => (eff.lookup op).map (op, ·)
        | _ => none
    let w := { w with hints := w.hints.push (do pure (.handler (← ρ) (← H))) }
    let w := match ρ, H, caps.mapM w.atomTy, (w.atomTy thunk).bind retOf with
      | some ρ, some H, some capTys, some σ => handlerUses env w ret ops capTys σ ρ H
      | _, _, _, _ => w
    go env depth f c (w.bind ρ false) body
  | .perform _ _ body => go env depth f c (w.bind none false) body
  | .label thunk body | .guard _ thunk body | .cell _ thunk body | .cellL _ _ thunk body | .lend _ _ thunk _ _ body =>
    go env depth f c (w.bind ((w.atomTy thunk).bind retOf) false) body
  | .cancel _ body => go env depth f c (w.bind (some .unit) false) body
  | .mem op args body => go env depth f c (w.bind (memTy env w.Γ op args) false) body
  | .host id args body =>
    let σ := hostTy id args w.atomTy ((said w.Γ.size).bind (tyOf env.decls w.binds))
    go env depth f c (w.bind σ (2 ≤ id)) body

/-- What a label's scope `g` gives, its body gone through with a label of a
result not known: what it ends with where that returns. -/
partial def labelRet (env : Env) (depth : Nat) (g : Nat) (binds : List (String × Ty)) (caps : List Ty) : Option Ty :=
  match fnRet env (depth + 1) g binds [.fn [.never] .never [] false none] caps with
  | some .never | none => none
  | r => r

/-- What `g` gives at what it is given and made with: its first clause's
that says. -/
partial def fnRet (env : Env) (depth : Nat) (g : Nat) (binds : List (String × Ty)) (params caps : List Ty)
    (stack : List Nat := []) : Option Ty := do
  if depth > 12 then none
  -- (Reached again while what it gives is being found: going on from here
  -- it does not return.)
  if stack.contains g then return .never
  let fn ← env.p.fns[g]?
  -- (A function of its own: its type parameters of what it is given.)
  let binds := match env.selfTy[g]? with
    | some (.fn ps _) => (ps.zip params).foldl (fun b (a, p) => matchTy env.decls b a p) []
    | _ => binds
  fn.clauses.zipIdx.findSome? fun (cl, ci) => do
    let bound ← patsTysD env.decls cl.pats params
    (go env depth g ci { Γ := (params ++ caps ++ bound).toArray.map some, binds, stack := g :: stack } cl.body).2

end

/-- The hints of every function at every signature `Typer` found, compared. -/
def compare (env : Env) (C : Types) : Tally := Id.run do
  let mut t : Tally := {}
  for e in C.sigs do
    let some fn := env.p.fns[e.fn]? | continue
    for ((cl, hs), ci) in (fn.clauses.zip e.hints).zipIdx do
      let bound := (patsTys C cl.pats e.sig.params).getD []
      let Γ : Array (Option Ty) := (e.sig.params ++ e.sig.caps ++ bound).toArray.map some
      -- (A function's type parameters, of what its parameters are said to be.)
      let binds := match env.decls.fns[e.fn]? with
        | some (tparams, annots, _) =>
          (annots.zip e.sig.params).foldl (fun b (a, p) => match a with
            | some te => matchTy env.decls b (rigidOf tparams te) p
            | none => b) []
        | none => []
      -- (And of what the checker found the function to be; a closure's, as
      -- where it was made.)
      let binds := binds ++ (t.closureBinds.getD (e.fn, e.sig.caps) []) ++ (t.calledBinds.getD (e.fn, e.sig.params) [])
      let binds := match env.selfTy[e.fn]? with
        | some (.fn ps r) => matchTy env.decls ((ps.zip e.sig.params).foldl (fun b (a, p) => matchTy env.decls b a p) binds) r e.sig.ret
        | _ => binds
      let (w, _) := go env 0 e.fn ci { Γ, binds, ret := some e.sig.ret } cl.body
      t := { t with closureBinds := w.made.foldl (fun m (k, b) => m.insert k b) t.closureBinds
                    calledBinds := w.called.foldl (fun m (k, b) => m.insert k b) t.calledBinds }
      if w.hints.size != hs.length then
        t := { t with lost := t.lost + 1 }
        continue
      let localOf : Std.HashMap Nat Nat := w.hintAt.fold (fun m i h => m.insert h i) {}
      for (mine, h) in w.hints.toList.zipIdx do
        if mine.isNone then
          let why := match localOf[h]? with
            | some i => match w.why[i]? with
              | some y => y
              | none => "call or host"
            | none => "handler"
          t := t.add s!"why: {why}" none
      for ((mine, theirs), h) in (w.hints.toList.zip hs).zipIdx do
        match theirs with
        | .ty σ =>
          let r := mine.map fun | .ty m => fits (shape m) (shape σ) | _ => false
          let ex := if r == some false then
              let d : String := match mine with
                | some (.ty m) => match diffAt (shape m) (shape σ) with
                  | some (x, y) => s!"here {Typer.showTy x}, Typer {Typer.showTy y}"
                  | none => "?"
                | _ => "?"
              some s!"{env.names[e.fn]?.getD "?"} local {(localOf[h]?).getD 0} ({(w.why[(localOf[h]?).getD 0]?).getD ""}): {d}"
            else if r.isNone && (t.counts.getD "nf" (0,0,0)).1 % 97 == 0 then
              some s!"not found: {env.names[e.fn]?.getD "?"} local {(localOf[h]?).getD 0} ({env.said[(e.fn, ci, (localOf[h]?).getD 0)]?.isSome}): Typer {Typer.showTy σ}"
            else none
          let t' := if r.isNone then t.add "nf" (some true) else t
          let kind := match σ with
            | .fn .. => "callable"
            | .data .. => "data"
            | .tuple _ => "tuple"
            | _ => "other"
          t := t'.add kind r ex
        | .handler ρ H =>
          let r := mine.map fun
            | .handler ρ' H' => (ρ' == .never || shape ρ' == shape ρ) && H' == H
            | _ => false
          let shown : Option String := mine.map fun
            | .handler ρ' H' => s!"{Typer.showTy ρ'} {H'.map (·.1)}"
            | _ => "?"
          let ex := if r == some false then some s!"{env.names[e.fn]?.getD "?"}: handler here {shown.getD "?"}, Typer {Typer.showTy ρ} {H.map (·.1)}" else none
          t := t.add "handler" r ex
  pure t

/-- The function a function the elaborator made is a copy of, by name:
`f⟨..⟩'` for implementations, `f@<..>` for an effect's instance. -/
def baseOf (owner : String) : String :=
  (((owner.splitOn "⟨").headD owner).splitOn "@<").headD owner

/-- The environment of a program for the forward typing. -/
def envOf (items : List Item) (out : Elab.Output) (nodeTys : Std.HashMap String (Std.HashMap Nat TypeExpr))
    (nodeInsts : Std.HashMap String (Std.HashMap Nat (List (String × Option TypeExpr))) := {}) :
    Except String Env := do
  let g ← Elab.collectDeclared items
  let decls := Typer.declsOf items g
  let said := out.fnNodes.fold (fun m f (owner, clauses) =>
    let base := baseOf owner
    match nodeTys[owner]? <|> nodeTys[base]? with
    | none => m
    | some tys => clauses.zipIdx.foldl (fun m (locals, c) =>
        locals.foldl (fun m (i, n) => match tys[n]? with
          | some te => m.insert (f, c, i) te
          | none => m) m) m) {}
  let selfTy := out.fnNodes.fold (fun m f (owner, _) =>
    if out.fnNames[f]? != some s!"`{owner}`" then m else
    let base := baseOf owner
    match (nodeTys[owner]? <|> nodeTys[base]?).bind (·[Flat.selfNode]?) with
    | some te => m.insert f te
    | none => m) {}
  let insts := out.fnNodes.fold (fun m f (owner, clauses) =>
    let base := baseOf owner
    match nodeInsts[owner]? <|> nodeInsts[base]? with
    | none => m
    | some is => clauses.zipIdx.foldl (fun m (locals, c) =>
        locals.foldl (fun m (i, n) => match is[n]? with
          | some ps => m.insert (f, c, i) ps
          | none => m) m) m) {}
  let implSelf := out.fnNodes.fold (fun m f (owner, _) =>
    if out.fnNames[f]? != some s!"`{owner}`" then m else
    let base := baseOf owner
    match (nodeTys[owner]? <|> nodeTys[base]?).bind (·[Flat.implSelfNode]?) with
    | some te => m.insert f te
    | none => m) {}
  let general := fun (te : TypeExpr) => (te.spell.splitOn "%rigid:").length > 1
  let settled := out.fnNodes.fold (fun s f (owner, _) =>
    let base := baseOf owner
    match (nodeTys[owner]? <|> nodeTys[base]?).bind (·[Flat.selfNode]?) with
    | some te => if general te then s else s.insert f
    | none => s) {}
  pure { decls, p := out.program, said, names := out.fnNames, selfTy, insts, implSelf, settled }

/-- A function's clause at a signature: its hints, the functions at the
signatures its closures are made at, and what it was found to give; an
error where a hint is not found. -/
def clauseAt (env : Env) (made called : Std.HashMap (Nat × List Ty) (List (String × Ty))) (fn ci : Nat)
    (cl : Core.Clause) (sig : FnSig) :
    Except String (List Hint × Array (Nat × FnSig) × Array ((Nat × List Ty) × List (String × Ty)) × Array ((Nat × List Ty) × List (String × Ty))) := do
  let some bound := patsTysD env.decls cl.pats sig.params
    | throw s!"function {fn}: what its patterns bind is not found, at {Typer.showSig sig}"
  let Γ : Array (Option Ty) := (sig.params ++ sig.caps ++ bound).toArray.map some
  let binds := match env.decls.fns[fn]? with
    | some (tparams, annots, _) =>
      (annots.zip sig.params).foldl (fun b (a, p) => match a with
        | some te => matchTy env.decls b (rigidOf tparams te) p
        | none => b) []
    | none => []
  let binds := binds ++ (made.getD (fn, sig.caps) []) ++ (called.getD (fn, sig.params) [])
  let binds := if env.settled.contains fn then binds ++ [("%settled", .unit)] else binds
  let binds := match env.selfTy[fn]? with
    | some (.fn ps r) => matchTy env.decls ((ps.zip sig.params).foldl (fun b (a, p) => matchTy env.decls b a p) binds) r sig.ret
    | _ => binds
  let (w, _) := go env 0 fn ci { Γ, binds, ret := some sig.ret, eff := sig.eff } cl.body
  let localOf : Std.HashMap Nat Nat := w.hintAt.fold (fun m i h => m.insert h i) {}
  let hints ← w.hints.toList.zipIdx.mapM fun (h, k) => match h with
    | some h => pure h
    | none =>
      let why := match localOf[k]? with
        | some i => s!"local {i}: {(w.why[i]?).getD "a call that does not return, or a host operation"}"
        | none => "a handler"
      throw s!"function {fn} ({env.names[fn]?.getD "?"}): hint {k} not found ({why})"
  pure (hints, w.uses, w.made, w.called)

/-- Core's types, found forward from the checker's (`Hints`), as `Typer`'s
are: each function at each signature a closure of it is made at, from
`main`, with each clause's hints, and the declared types and operations
those use. -/
def typesOf (items : List Item) (out : Elab.Output) (nodeTys : Std.HashMap String (Std.HashMap Nat TypeExpr))
    (nodeInsts : Std.HashMap String (Std.HashMap Nat (List (String × Option TypeExpr))) := {}) :
    Except String Types := do
  let env ← envOf items out nodeTys nodeInsts
  let p := out.program
  -- (`main`: run with nothing, performing nothing.)
  let (w, mainTy) := go env 0 p.fns.size 0 { binds := [("%settled", .unit)] } p.main
  let some mainTy := mainTy | throw "what `main` gives is not found"
  let localOf : Std.HashMap Nat Nat := w.hintAt.fold (fun m i h => m.insert h i) {}
  let mainHints ← w.hints.toList.zipIdx.mapM fun (h, k) => match h with
    | some h => pure h
    | none => throw s!"a hint of `main` not found ({(localOf[k]?.bind (w.why[·]?)).getD "?"})"
  let mut todo : List (Nat × FnSig) := w.uses.toList
  let mut made : Std.HashMap (Nat × List Ty) (List (String × Ty)) := w.made.foldl (fun m (k, b) => m.insert k b) {}
  let mut called : Std.HashMap (Nat × List Ty) (List (String × Ty)) := w.called.foldl (fun m (k, b) => m.insert k b) {}
  let mut emitted : Std.HashMap Nat (List FnSig) := {}
  let mut sigs : Array SigEntry := #[]
  let mut fuel := 1000000
  while !todo.isEmpty && fuel > 0 do
    fuel := fuel - 1
    match todo with
    | (fn, sig) :: rest =>
      todo := rest
      let key := { sig with eff := [] }
      if (emitted.getD fn []).contains key then continue
      emitted := emitted.insert fn (key :: emitted.getD fn [])
      let some f := p.fns[fn]? | throw s!"function {fn} does not exist"
      let mut hints : List (List Hint) := []
      let mut uses : Array (Nat × FnSig) := #[]
      for (cl, ci) in f.clauses.zipIdx do
        let (hs, us, ms, cs) ← clauseAt env made called fn ci cl sig
        hints := hints ++ [hs]
        uses := uses ++ us
        made := ms.foldl (fun m (k, b) => m.insert k b) made
        called := cs.foldl (fun m (k, b) => m.insert k b) called
      sigs := sigs.push ⟨fn, sig, hints⟩
      todo := uses.toList ++ todo
      -- (What destroys a closure of it, at what destroys one of these.)
      if let some d := p.drops.lookup fn then
        todo := todo ++ [(d, dropSig sig)]
    | [] => pure ()
  let types := mainTy :: mainHints.flatMap hintTypes ++ sigs.toList.flatMap fun e =>
    e.sig.caps ++ e.sig.params ++ [e.sig.ret] ++ e.sig.eff.flatMap (·.2) ++ e.hints.flatMap (·.flatMap hintTypes)
  let rows := sigs.toList.flatMap fun e => e.sig.eff ++ e.hints.flatMap (·.flatMap hintOps)
  let tenv : Typer.Env := { decls := env.decls, p, ncaps := #[] }
  let (datas, ops) ← match ((Typer.declsFor types (rows ++ mainHints.flatMap hintOps)).run tenv).run {} with
    | .ok r _ => pure r
    | .error e _ => throw e
  pure (Types.withIndex ⟨sigs, datas, ops, mainTy, mainHints, #[]⟩)
where
  hintTypes : Hint → List Ty
    | .ty t => [t]
    | .handler ρ H => ρ :: H.flatMap (·.2)
  hintOps : Hint → List (Nat × List Ty)
    | .handler _ H => H
    | _ => []

/-- Typer's signatures and these, compared (`GLORIOUS_TRACE=hintsigs`). -/
def compareSigs (items : List Item) (out : Elab.Output) (nodeTys : Std.HashMap String (Std.HashMap Nat TypeExpr))
    (nodeInsts : Std.HashMap String (Std.HashMap Nat (List (String × Option TypeExpr)))) (C : Types) : String :=
  match typesOf items out nodeTys nodeInsts with
  | .error e => s!"hintsigs: none: {e}"
  | .ok D => Id.run do
    let theirs : Std.HashMap Nat (List FnSig) := C.sigs.foldl (fun m e => m.insert e.fn (e.sig :: m.getD e.fn [])) {}
    let mine : Std.HashMap Nat (List FnSig) := D.sigs.foldl (fun m e => m.insert e.fn (e.sig :: m.getD e.fn [])) {}
    let mut lines : Array String := #[s!"hintsigs: Typer {C.sigs.size}, here {D.sigs.size}; main {Typer.showTy C.mainTy} / {Typer.showTy D.mainTy}"]
    for (fn, ts) in theirs.toList do
      let ms := mine.getD fn []
      for t in ts do
        unless ms.contains t do
          if lines.size < 30 then
            lines := lines.push s!"  {out.fnNames[fn]?.getD "?"}: Typer's {Typer.showSig t} not here; here {ms.map Typer.showSig}"
    for (fn, ms) in mine.toList do
      let ts := theirs.getD fn []
      for m in ms do
        unless ts.contains m do
          if lines.size < 60 then
            lines := lines.push s!"  {out.fnNames[fn]?.getD "?"}: here {Typer.showSig m} not Typer's"
    "\n".intercalate lines.toList

/-- `compare`, said. -/
def report (items : List Item) (out : Elab.Output) (nodeTys : Std.HashMap String (Std.HashMap Nat TypeExpr))
    (C : Types) : String := Id.run do
  let some g := (Elab.collectDeclared items).toOption | return "hints: no declarations"
  let decls := Typer.declsOf items g
  let said := out.fnNodes.fold (fun m f (owner, clauses) =>
    let base := baseOf owner
    match nodeTys[owner]? <|> nodeTys[base]? with
    | none => m
    | some tys => clauses.zipIdx.foldl (fun m (locals, c) =>
        locals.foldl (fun m (i, n) => match tys[n]? with
          | some te => m.insert (f, c, i) te
          | none => m) m) m) {}
  let selfTy := out.fnNodes.fold (fun m f (owner, _) =>
    if out.fnNames[f]? != some s!"`{owner}`" then m else
    let base := baseOf owner
    match (nodeTys[owner]? <|> nodeTys[base]?).bind (·[Flat.selfNode]?) with
    | some te => m.insert f te
    | none => m) {}
  let t := compare { decls, p := out.program, said, names := out.fnNames, selfTy } C
  let lines := t.counts.toList.map fun (k, (a, d, u)) => s!"  {k}: {a} agree, {d} not, {u} not found"
  "\n".intercalate ([s!"hints: {t.lost} clauses lost"] ++ lines ++ t.examples.toList.map ("  " ++ ·))

end Glorious.Hints
