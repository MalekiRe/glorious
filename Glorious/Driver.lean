module

public import Glorious.Trace
public import Glorious.Syntax.Parser
public import Glorious.Syntax.Resolve
public import Glorious.Syntax.Modules
public import Glorious.Elab
public import Glorious.Elab.Instances
public import Glorious.Elab.Specialize
public import Glorious.Check
public import Glorious.Infer
public import Glorious.Prelude
public import Glorious.Std
public import Glorious.Compile
public import Glorious.Core.Semantics
public import Glorious.Core.Cleanup
public import Glorious.Bytecode.Semantics
public import Glorious.Bytecode.Encode

/-!
# Driver

Source text to Core, and helpers to run a program on both machines.
-/

public section

namespace Glorious

structure Compiled where
  core : Core.Program
  ctorNames : Array String
  fnNames : Array String
  opNames : Array String
  /-- The typing of `core` that `Typing.checkProgram` accepted, when the program
  was checked. With it, `Typing.checked_safety` applies to `core`; if the
  certificate is `strict`, so does `Typing.checked_owned_safety`; and if it has
  `regions`, so does `Typing.checked_borrow_safety`; and if it has `loans`,
  so does `Typing.checked_exclusive_safety`. -/
  cert : Option Typing.Cert := none
  /-- How many borrows are scopes of their own in `core`: those written as
  arguments of calls of functions, if the program could then be shown to
  follow the rules for borrows. `checked_exclusive_safety` is about these. -/
  lent : Nat := 0
  /-- The borrows that are not: each is, in `core`, the reference it borrows,
  and only the check of the source text keeps it exclusive. -/
  plain : List Elab.Borrow := []
  /-- How each place of `core` was elaborated (0 for a borrow that is the
  reference it borrows, and 1 or 2 for a scope of its own), by the function it
  is in and how many places of that function come before it: what a later
  compile of a changed program can start from. -/
  places : List ((String × Nat) × Nat) := []
  /-- What the checker kept, for a later compile of the program in the same
  process (`Check.Kept`). -/
  checkKept : Check.Kept := []
  /-- What certificate inference made, for a later compile (`Infer.Memo`). -/
  inferMade : Infer.Made := {}
  /-- The prelude (and library) as checked, where this compile checked it:
  for a later process, by whether the library is in and whether `Drop` is. -/
  firstMade : Option ((Bool × Bool) × (Nat × Check.St)) := none
  /-- What the checker kept of the library's modules, for any program that
  begins with them. -/
  libraryKept : Check.Kept := []

/-- Each place by the function it is in and how many places of that function
come before it: what stays the same of a place when other functions change. -/
def placeKeys (owners : Array String) : Array (String × Nat) := Id.run do
  let mut count : Std.HashMap String Nat := {}
  let mut out := #[]
  for o in owners do
    let k := count.getD o 0
    out := out.push (o, k)
    count := count.insert o (k + 1)
  pure out

mutual
/-- Every name an expression writes, bound or not, and every field or function
named after a dot: more than it can mean, never less. -/
partial def namesInExpr (acc : List String) : Syntax.Expr → List String
  | .name _ n => n :: acc
  | .call _ f args => args.foldl namesInExpr (namesInExpr acc f)
  | .tailCall _ f args => args.foldl namesInExpr (namesInExpr acc f)
  | .tuple args => args.foldl namesInExpr acc
  | .proj e _ => namesInExpr acc e
  | .closure _ clauses => clauses.foldl namesInClause acc
  | .handle subject arms => arms.foldl namesInClause (namesInExpr acc subject)
  | .labelScope _ body => body.foldl namesInStmt acc
  | .ref _ n => n :: acc
  | .deref e => namesInExpr acc e
  | .reborrow _ e => namesInExpr acc e
  | .refField _ _ n path _ => n :: path ++ acc
  | .fieldOf _ e n => namesInExpr (n :: acc) e
  | .int _ => acc
  | .label _ => acc

partial def namesInStmt (acc : List String) : Syntax.Stmt → List String
  | .let_ _ value => namesInExpr acc value
  | .expr e => namesInExpr acc e
  | .defer e => namesInExpr acc e
  | .letMut _ value => namesInExpr acc value
  | .assign target value => namesInExpr (namesInExpr acc target) value
  | .located _ _ s => namesInStmt acc s

partial def namesInClause (acc : List String) : Syntax.Clause → List String
  | .mk _ body => body.foldl namesInStmt acc
end

mutual
/-- The identities of an expression's calls. -/
partial def callIdsExpr (acc : List Nat) : Syntax.Expr → List Nat
  | .call id f args => args.foldl callIdsExpr (callIdsExpr (id :: acc) f)
  | .tailCall id f args => args.foldl callIdsExpr (callIdsExpr (id :: acc) f)
  | .tuple args => args.foldl callIdsExpr acc
  | .proj e _ => callIdsExpr acc e
  | .closure _ clauses => clauses.foldl callIdsClause acc
  | .handle subject arms => arms.foldl callIdsClause (callIdsExpr acc subject)
  | .labelScope _ body => body.foldl callIdsStmt acc
  | .deref e => callIdsExpr acc e
  | .reborrow _ e => callIdsExpr acc e
  | .fieldOf _ e _ => callIdsExpr acc e
  | _ => acc

partial def callIdsStmt (acc : List Nat) : Syntax.Stmt → List Nat
  | .let_ _ value => callIdsExpr acc value
  | .expr e => callIdsExpr acc e
  | .defer e => callIdsExpr acc e
  | .letMut _ value => callIdsExpr acc value
  | .assign target value => callIdsExpr (callIdsExpr acc target) value
  | .located _ _ s => callIdsStmt acc s

partial def callIdsClause (acc : List Nat) : Syntax.Clause → List Nat
  | .mk _ body => body.foldl callIdsStmt acc

partial def callIdsItem (acc : List Nat) : Syntax.Item → List Nat
  | .fn _ _ _ _ clauses => clauses.foldl callIdsClause acc
  | .impl _ _ _ _ _ methods => methods.foldl callIdsItem acc
  | .traitInfo _ _ defaults _ _ => defaults.foldl callIdsItem acc
  | .alias _ value => callIdsExpr acc value
  | .pub _ item => callIdsItem acc item
  | _ => acc
end

/-- What of a program's modules a unit's check reads besides its own items:
the coercions that apply in it, the dot calls among its calls the resolver
found more than one function for, and which fields of the constructors of it
and of the units before it are `pub`. -/
def unitInfoKey (info : Syntax.ModuleInfo) (before : List String) (unit : String)
    (items : List Syntax.Item) : UInt64 :=
  let ids : Std.HashSet Nat := items.foldl (fun set i => (callIdsItem [] i).foldl (·.insert ·) set) {}
  let alts := info.dotAlts.filter fun (id, _) => ids.contains id
  let seen := unit :: before
  let vis := info.fieldVis.filter fun (_, home, _) => seen.contains home
  hash (unit, info.coercions.lookup unit, alts, vis, info.text, info.shadowed)

/-- The names written in an item that is not one of the library's functions. -/
partial def namesInItem (acc : List String) : Syntax.Item → List String
  | .fn _ _ _ _ clauses => clauses.foldl namesInClause acc
  | .impl _ _ _ _ _ methods => methods.foldl namesInItem acc
  | .traitInfo _ _ defaults _ _ => defaults.foldl namesInItem acc
  | .alias _ value => namesInExpr acc value
  | .coerce name => name :: acc
  | .pub _ item => namesInItem acc item
  | .module _ (some body) => body.foldl namesInItem acc
  | _ => acc

/-- The library's modules read for one program, without the functions none of
the program's text can reach: each is kept if its name, without its module, is
written in what is kept. (They are known to be well typed: the library is
checked whole by the tests. A function its text names but nothing calls is
kept, and so checked, as it was.) -/
partial def withoutUnreached (items : List Syntax.Item) : List Syntax.Item := Id.run do
  let library := fun (name : String) =>
    name.startsWith "std::" || name.startsWith "core::" || name.startsWith "alloc::"
  let isLibraryFn : Syntax.Item → Option String
    | .fn name _ _ _ _ => if library name then some (Syntax.lastSegment name) else none
    | _ => none
  let mut wanted : Std.HashSet String := {}
  for item in items do
    if (isLibraryFn item).isNone then
      for n in namesInItem [] item do wanted := wanted.insert (Syntax.lastSegment n)
  let mut kept : Std.HashSet Nat := {}
  let mut changed := true
  let indexed := items.zipIdx
  while changed do
    changed := false
    for (item, k) in indexed do
      if let some short := isLibraryFn item then
        if !kept.contains k && wanted.contains short then
          kept := kept.insert k
          changed := true
          for n in namesInItem [] item do wanted := wanted.insert (Syntax.lastSegment n)
  pure <| indexed.filterMap fun (item, k) =>
    if (isLibraryFn item).isSome && !kept.contains k then none else some item

/-- The functions an error of certificate inference names: `function 12`. -/
def named (e : String) : List Nat :=
  ((e.splitOn "function ").drop 1).filterMap fun after =>
    (String.ofList (after.toList.takeWhile Char.isDigit)).toNat?

/-- What certificate inference or the checker of certificates said, with each
function it names (`function 12`) followed by what that function is. -/
def withFnNames (names : Array String) (e : String) : String :=
  match e.splitOn "function " with
  | [] => e
  | first :: rest => first ++ String.join (rest.map fun after =>
      let digits := (after.takeWhile Char.isDigit).toString
      match digits.toNat? with
      | some n => s!"function {digits} ({(names[n]?).getD "?"})" ++ (after.drop digits.length).toString
      | none => "function " ++ after)

/-- A certificate for `p` with these rules, and whether the proved checker
accepts it: one of `kept` (what an earlier compile found) if the checker
accepts it for `p`, and otherwise one found by inference, taking what an
earlier compile kept of its inference (`memo`) and giving what this one made
(nothing, where a kept certificate passed). Where what comes of `memo` is
turned away, it is looked for afresh: what is kept makes a compile faster,
never different. -/
def certifyWith (kept : List Typing.Cert) (items : List Syntax.Item) (p : Core.Program)
    (strict : Bool) (envSizes : List (Nat × Nat × Nat)) (regions loans ranked widen : Bool)
    (memo : Infer.Memo := {}) : Except String (Typing.Cert × Bool × Infer.Made) :=
  match kept.find? fun c =>
      c.strict == strict && c.regions == regions && c.loans == loans && Typing.checkProgram c p with
  | some c => .ok (c, true, {})
  | none =>
    let infer := fun (memo : Infer.Memo) =>
      (Infer.certifyKept items p strict envSizes regions loans ranked widen memo).map fun (cert, made) =>
        (cert, Typing.checkProgram cert p, made)
    match infer memo with
    | .ok (cert, true, made) => .ok (cert, true, made)
    | other => if memo.isEmpty then other else infer {}

/-- Find a certificate for a program's Core and have the proved checker accept
it: with the ownership rules and the region rules if the program can be shown
to meet them, and otherwise with those of them it can, or as a typing only.
An error here is a defect in the compiler, not in the program. -/
def certifyProgram (items : List Syntax.Item) (p : Core.Program)
    (envSizes : List (Nat × Nat × Nat) := []) (failed : List (Bool × Bool) := [])
    (first : Option Nat := none) (kept : List Typing.Cert := []) (memo : Infer.Memo := {}) :
    Except String (Typing.Cert × Option Nat × Infer.Made) := do
  -- With the region rules, first with callables taken to bind a region
  -- where they are given a reference to a cell, and then without; and only
  -- then with references taken to be to one of several cells where they
  -- have to be.
  -- (What was kept of an earlier compile's inference is taken first; if
  -- what comes of it is turned away, the certificate is looked for afresh.)
  let one (strict regions loans ranked widen : Bool) : Option (Typing.Cert × Infer.Made) :=
    match certifyWith kept items p strict envSizes regions loans ranked widen memo with
    | .ok (cert, true, made) => some (cert, made)
    | _ => none
  -- (`failed`: ways already seen to fail with every rule, not tried again.
  -- `first`: the one of these attempts that passed last time, tried first.)
  let ways := [(true, false), (false, false), (false, true), (true, true)]
  let rules := [(true, true, true), (true, true, false), (true, false, false), (false, true, true),
    (false, true, false)]
  let attempts := rules.flatMap fun (strict, regions, loans) =>
    (if regions then ways else [(false, false)]).map fun (ranked, widen) =>
      (strict, regions, loans, ranked, widen)
  let try_ := fun (k : Nat) => match attempts[k]? with
    | some (strict, regions, loans, ranked, widen) =>
      if strict && regions && loans && failed.contains (ranked, widen) then none
      else Trace.timed s!"certificate way {k}" fun _ => one strict regions loans ranked widen
    | none => none
  -- (The one that passed last time, or else the first; and if that does
  -- not pass, the others all at once, each on a thread of its own, the
  -- first of them in order that passes taken.)
  let start := first.getD 0
  if let some (cert, made) := try_ start then return (cert, some start, made)
  let others := (List.range attempts.length).filter (· != start)
  let tasks := others.map fun k => (k, Task.spawn fun _ => try_ k)
  if let some found := tasks.findSome? fun (k, t) => t.get.map fun (cert, made) => (cert, some k, made) then
    return found
  let cert ← match Infer.certify items p false envSizes with
    | .ok cert => pure cert
    | .error e => throw s!"no certificate was found: {e}"
  if Typing.checkProgram cert p then pure (cert, none, {})
  else throw s!"the certificate was rejected: {Infer.rejected cert p}"

/-- What the specification's default prelude has that this one keeps in the
library (§3): each name, with its module. -/
def stdPreludeNames : List (String × String) :=
  [("identity", "value"), ("discard", "value"), ("Either", "value"),
   ("Left", "value"), ("Right", "value"), ("Rejected", "value"), ("Ordering", "cmp"),
   ("Less", "cmp"), ("Equal", "cmp"), ("Greater", "cmp"), ("Range", "iterator"),
   ("Fail", "value"), ("fail", "value"), ("Report", "value"), ("report", "value"),
   ("catch_fail", "value"), ("Vec", "vec"), ("String", "text"), ("Iterator", "iterator")]

/-- The names of the default prelude a program's text uses and does not
declare or bring in itself: `use` lines for them, written after the text (so
that no position in it moves). Where the text names no library, none. -/
def stdPreludeUses (src : String) : String := Id.run do
  -- (Nor where the text brings in whole modules, whose names could be any.)
  if (src.splitOn "#![no_std]").length > 1 || (src.splitOn "#![no_implicit_prelude]").length > 1
      || (src.splitOn "mod std").length > 1 || (src.splitOn "::*").length > 1 then
    return ""
  let isWord := fun (c : Char) => c.isAlphanum || c == '_'
  -- (Written as a name of its own: not after `::`, `.` or another letter,
  -- nor before one.)
  let mentions := fun (name : String) => Id.run do
    let parts := src.splitOn name
    let mut found := false
    for (before, after) in parts.zip (parts.drop 1) do
      let prev := before.toList.getLast?
      let next := after.toList.head?
      let okBefore := match prev with
        | some c => !isWord c && c != '.' && c != ':'
        | none => true
      let okAfter := match next with
        | some c => !isWord c
        | none => true
      if okBefore && okAfter then found := true
    pure found
  let declares := fun (name : String) =>
    ["fn ", "enum ", "struct ", "type ", "trait ", "effect ", "const ", "let "].any fun k =>
      (src.splitOn (k ++ name)).length > 1
  -- (What the text's `use`s name, `use m::{a, b};` too.)
  let uses := (src.splitOn "use ").drop 1 |>.map fun after => (after.splitOn ";").headD ""
  let inUse := fun (name : String) => uses.any fun u =>
    let parts := u.splitOn name
    (parts.zip (parts.drop 1)).any fun (before, after) =>
      (before.toList.getLast?.all fun c => !isWord c) && (after.toList.head?.all fun c => !isWord c)
  let brought := fun (name : String) =>
    (src.splitOn ("::" ++ name)).length > 1 || inUse name
  -- (An operation goes with its effect: where the text declares the effect,
  -- or an operation of the name in an effect of its own, neither is.)
  let opOf : List (String × String) := [("fail", "Fail"), ("report", "Report")]
  let ownOp := fun (name : String) =>
    (src.splitOn "effect ").drop 1 |>.any fun after =>
      let body := ((after.splitOn "}").headD "")
      (body.splitOn (name ++ "(")).length > 1
  let blocked := fun (name : String) =>
    declares name || brought name || ownOp name
      || (opOf.lookup name).any (fun e => declares e || brought e)
      || (opOf.find? (·.2 == name)).any (fun (op, _) => ownOp op)
  let wanted := stdPreludeNames.filter fun (name, _) => mentions name && !blocked name
  if wanted.isEmpty then return ""
  let mods := wanted.map (·.2) |>.eraseDups
  let lines := mods.map fun m =>
    s!"use std::{m}::\{{", ".intercalate ((wanted.filter (·.2 == m)).map (·.1))}};"
  return "\n" ++ "\n".intercalate lines ++ "\n"

/-- Does a program have the standard library: does it name `std`, and have no
module `std` of its own? -/
def usesStd (src : String) (files : List (List String × String)) : Bool :=
  let named := fun (text : String) =>
    (text.splitOn "std").length > 1 || (text.splitOn "core::").length > 1
      || (text.splitOn "alloc::").length > 1
  let own := fun (text : String) =>
    (text.splitOn "mod std {").length > 1 || (text.splitOn "mod std{").length > 1
  (named src || files.any fun (_, text) => named text)
    && !own src && !files.any fun (path, _) => path.head? == some "std"

/-- An `unsafe trait` is implemented with `unsafe impl`, and nothing else is. -/
partial def checkUnsafeImpls (items : List Syntax.Item) : Except String Unit := do
  let rec flat : List Syntax.Item → List Syntax.Item
    | [] => []
    | .pub _ i :: rest => flat (i :: rest)
    | .module _ (some body) :: rest => flat body ++ flat rest
    | i :: rest => i :: flat rest
  let all := flat items
  let last := fun (s : String) => (s.splitOn "::").getLast!
  let traits := all.filterMap fun
    | .fieldNames mark [name] _ => if mark == Syntax.attrMark "unsafe_trait" then some name else none
    | _ => none
  let promised := all.filterMap fun
    | .fieldNames mark [tr, head] _ =>
      if mark == Syntax.attrMark "unsafe_impl" then some (last tr, last head) else none
    | _ => none
  -- `impl !Trait for Type {}`: no implementation says otherwise.
  let denied := all.filterMap fun
    | .fieldNames mark [tr, head] _ =>
      if mark == Syntax.attrMark "negative_impl" then some (last tr, last head) else none
    | _ => none
  for item in all do
    if let .impl _ tr head _ _ _ := item then
      if denied.contains (last tr, last head) then
        throw s!"`{last head}` is said not to have `{last tr}` (`impl !{last tr} for {last head}`), and an implementation says it does"
  for item in all do
    if let .impl _ tr head _ _ _ := item then
      let said := promised.contains (last tr, last head)
      if traits.contains (last tr) && !said then
        throw s!"`{last tr}` is an `unsafe trait`: its implementation for `{last head}` is written `unsafe impl {last tr} for {last head}`"
      if !traits.contains (last tr) && said then
        throw s!"`unsafe impl {last tr} for {last head}`: `{last tr}` is not an `unsafe trait`"

/-- The prelude read, once. -/
def readPrelude : Thunk (Except String (List Syntax.Item × Syntax.Fixities)) := Thunk.mk fun _ =>
  match Syntax.parse {} Prelude.source with
  | .ok r => .ok r
  | .error e => .error s!"prelude: {e}"

/-- The library's texts read, once: what each says before it is parsed, the
operators of each of its modules in a program that declares none, every
name written in the texts, and each text parsed. A program that names the
library reads them the same, unless it has a constructor with named fields
whose name the library's texts write, or brings an operator into one of the
library's modules: then they are read again for that program. -/
structure StdRead where
  said : List Syntax.TextSyntax
  records : List String
  names : Std.HashSet String
  tables : List (List String × Syntax.Fixities)
  parsed : Array (List Syntax.Item)

def readStd : Thunk (Except String StdRead) := Thunk.mk fun _ => do
  let (_, fix) ← readPrelude.get
  let syn ← Std.texts.mapM fun (path, text) => Syntax.textSyntax path text
  let records := syn.flatMap (·.records)
  let tables ← Syntax.joinFixities fix ((← Syntax.textSyntax [] "") :: syn)
  let mut parsed : Array (List Syntax.Item) := #[]
  for ((path, text), k) in Std.texts.zipIdx do
    match Syntax.parse fix text (base := 1000000 * (k + 2)) (records := records) (tables := tables)
        (path := path) with
    | .ok (items, _) => parsed := parsed.push items
    | .error e => throw s!"module `{"::".intercalate path}`: {e}"
  let names := syn.foldl (fun set s => s.names.foldl (fun set n => set.insert n) set) {}
  pure { said := syn, records := records, names := names, tables := tables, parsed := parsed }

/-- Does a text write a length in brackets, `[T; N]` or `[x; n]`: a `;`
with only a name or a number between it and the `]`? -/
def saysLength (text : String) : Bool :=
  (text.splitOn ";").drop 1 |>.any fun piece =>
    match piece.splitOn "]" with
    | before :: _ :: _ =>
      let word := before.trimAscii.toString
      !word.isEmpty && word.all fun c => c.isAlphanum || c == '_'
    | _ => false

/-- The library's modules a program needs: those its texts name after
`std::`, `core::` or `alloc::`, and those that these name in turn; with the
texts of the three roots cut down to them. Nothing where the texts name the
library some other way (`use std::{a, b}`), and all of it is then read. -/
def neededStd (texts : List String) : Option (List (List String × String)) :=
  let roots := ["std", "core", "alloc"]
  if texts.any (fun text => roots.any fun r => (text.splitOn s!"{r}::\{").length > 1
      || (text.splitOn s!"{r}::*").length > 1 || (text.splitOn s!"use {r};").length > 1) then none
  else
    let named := fun (text : String) => roots.flatMap fun r =>
      ((text.splitOn s!"{r}::").drop 1).map fun after =>
        [r, String.ofList (after.toList.takeWhile fun c => c.isAlphanum || c == '_')]
    let rec close (fuel : Nat) (have_ todo : List (List String)) : List (List String) :=
      match fuel, todo with
      | 0, _ => have_
      | _, [] => have_
      | fuel + 1, path :: rest =>
        if have_.contains path then close fuel have_ rest
        else match Std.texts.lookup path with
          | some text => close fuel (path :: have_) (named text ++ rest)
          | none => close fuel have_ rest
    let needed := close 4096 [] (texts.flatMap named)
    -- (With the modules inside each, and what those name.)
    let inside := fun (have_ : List (List String)) =>
      (Std.texts.filter fun (path, _) => have_.any fun p => p.length < path.length && p.isPrefixOf path)
    let needed := close 4096 needed
      (((inside needed).map (·.1)) ++ (inside needed).flatMap fun (_, text) => named text)
    let needed := needed ++ ((inside needed).map (·.1)).filter (!needed.contains ·)
    if needed.isEmpty then some []
    else
      -- (A root says only which of its modules there are.)
      let rootOf := fun (r : String) =>
        (needed.filter fun path => path.head? == some r && path.length == 2).foldl (fun text path =>
          text ++ s!"pub mod {path.getLastD ""};\n") ""
      let usedRoots := roots.filter fun r => needed.any (·.head? == some r)
      some (usedRoots.map (fun r => ([r], rootOf r))
        ++ Std.texts.filter fun (path, _) => needed.contains path)

/-- The library's texts, each lexed once in a process, where it is first
read: a compile reads a module's tokens three times (for its fixities, its
syntax and its items). -/
def stdLexed : List (List String × Thunk (Except String (Array Syntax.Token))) :=
  Std.texts.map fun (path, text) => (path, Thunk.mk fun _ => Syntax.lex text)

/-- A library module's tokens, if this is its text as the library has it (a
compile that reads only some modules reads a root that names only those). -/
def stdTokens (path : List String) (text : String) : Option (Array Syntax.Token) :=
  if (Std.texts.lookup path) != some text then none else
  (stdLexed.lookup path).bind fun th => match th.get with
    | .ok toks => some toks
    | .error _ => none

/-- A program's own texts lexed: the first module's under the empty path. -/
def lexTexts (src : String) (files : List (List String × String)) :
    Except String (List (List String × Array Syntax.Token)) :=
  (([], src) :: files).mapM fun (path, text) => do pure (path, ← Syntax.lex text)

/-- The longest list of types any of them writes, and at least two. -/
def longestOf (lexed : List (List String × Array Syntax.Token)) : Nat :=
  lexed.foldl (fun m (_, toks) => max m (Syntax.longestList toks)) 2

/-- The prelude and a program as written: the first module's text, and the
texts of the modules that are files of their own, each with its path. Where
the program says `mod name;` the items of that module's text are put. -/
def parseProgram (src : String) (files : List (List String × String)) (check : Bool := true)
    (few : Bool := false) (packs : Nat := 0) (lexed : List (List String × Array Syntax.Token) := []) :
    Except String (List Syntax.Item × List Syntax.Item) := do
  -- (The program's own texts lexed once, where they were not already.)
  let lexed ← if !lexed.isEmpty then pure lexed else lexTexts src files
  let tokensOf := fun (path : List String) => lexed.lookup path
  -- Lists of types are written out to the longest list the program's texts
  -- write, unless told longer.
  let packs := if packs != 0 then packs else longestOf lexed
  -- The library's texts are files of the program, before its own.
  -- (`#![no_std]`: without the library, whatever the text mentions.)
  let std := usesStd src files && (src.splitOn "#![no_std]").length == 1
  let own := files
  -- (`few`: only the library's modules the program needs, read and checked
  -- with it, where it is one program that is compiled: the whole library
  -- read once serves many.)
  let needed := if few && std then neededStd (src :: own.map (·.2)) else none
  let library := needed.getD Std.texts
  let files := if std then library ++ files else files
  let (prelude, fix) ← if check then readPrelude.get else
    match Syntax.parse {} Prelude.unchecked with
    | .ok r => pure r
    | .error e => throw s!"prelude: {e}"
  -- The library's texts as they were read once, where the program names it.
  let read ← if std && check && needed.isNone then
      (do pure (some (← readStd.get)) : Except String (Option StdRead))
    else pure none
  -- Operators and the constructors with named fields are known to every
  -- text, whichever declares them.
  let said ← (([], src) :: own).mapM fun (path, text) => do
    let _ ← Syntax.declaredSyntax fix text (tokensOf path)
    Syntax.textSyntax path text (tokensOf path)
  let unread ← match read with
    | some _ => pure []
    | none => (if std then library else []).mapM fun (path, text) => do
        let lexed := stdTokens path text
        let _ ← Syntax.declaredSyntax fix text lexed
        Syntax.textSyntax path text lexed
  let librarySaid := match read with
    | some r => r.said
    | none => unread
  let ordered := said.take 1 ++ librarySaid ++ said.drop 1
  let records := ordered.flatMap (·.records)
  -- An operator's fixity is its module's.
  let tables ← Syntax.joinFixities fix ordered
  -- The library as it was read once is the library as this program reads
  -- it, if none of the program's own constructors with named fields is a
  -- name the library writes, and its modules have the operators they had.
  let kept : Option StdRead := read.bind fun r =>
    let mine := said.flatMap (·.records)
    if mine.any r.names.contains then none
    else if r.tables.all fun (p, table) => p.isEmpty || tables.lookup p == some table then some r
    else none
  -- Whether the program has arrays of a length their type says: then what
  -- `[a, b, c]` is depends on what is wanted of it.
  let fixed := ((src :: own.map (·.2)).any saysLength)
  let (items, _) ← Syntax.parse fix src (base := 1000000) (records := records) (tables := tables)
    (fixed := fixed) (packs := packs) (lexed := tokensOf [])
  let declares := items.any fun
    | .module "std" _ | .pub _ (.module "std" _) => true
    | _ => false
  -- (`core` and `alloc` are the library's too: its other names for the same.)
  let items := if std && !declares then
      items ++ (["std", "core", "alloc"].filter fun r => library.any (·.1 == [r])).map fun r =>
        Syntax.Item.pub false (.module r none)
    else items
  let rec fill (fuel : Nat) (path : List String) (items : List Syntax.Item) :
      Except String (List Syntax.Item) :=
    items.mapM fun item => do
      let (wrap, inner) : (Syntax.Item → Syntax.Item) × Syntax.Item := match item with
        | .pub parent i => (Syntax.Item.pub parent, i)
        | i => (id, i)
      match inner, fuel with
      | .module name none, fuel + 1 =>
        let here := path ++ [name]
        let shown := "::".intercalate here
        match files.findIdx? (·.1 == here) with
        | some k =>
          let parsed ← match (if k < library.length then kept.bind (·.parsed[k]?) else none) with
            | some items => pure items
            | none =>
              let text := ((files[k]?).map (·.2)).getD ""
              match Syntax.parse fix text (base := 1000000 * (k + 2)) (records := records)
                  (tables := tables) (path := here) (fixed := fixed && k ≥ (if std then library.length else 0))
                  (packs := packs) (lexed := if k < library.length then stdTokens here text else tokensOf here) with
              | .ok (items, _) => pure items
              | .error e => throw s!"module `{shown}`: {e}"
          pure (wrap (.module name (some (← fill fuel here parsed))))
        | none => throw s!"module `{shown}` has no file"
      | .module name (some body), fuel + 1 =>
        pure (wrap (.module name (some (← fill fuel (path ++ [name]) body))))
      | _, _ => pure item
  let items ← fill 64 [] items
  checkUnsafeImpls items
  pure (prelude, items)

/-- A program's items as the resolver gives them, each module's after a mark
(`Syntax.unitMark`), put in an order that has every module after those it
uses, the prelude's items first and the library's modules before the
program's: the items before the first mark, and each module's key and items. -/
def unitsOf (items : List Syntax.Item) (uses : List (String × List String)) :
    List Syntax.Item × List (String × List Syntax.Item) := Id.run do
  let mark : Syntax.Item → Option String
    | .fieldNames m [k] [] => if m == Syntax.unitMark then some k else none
    | _ => none
  let first := items.takeWhile fun i => (mark i).isNone
  let mut units : Array (String × Array Syntax.Item) := #[]
  for i in items.drop first.length do
    match mark i with
    | some k => units := units.push (k, #[])
    | none =>
      if units.size > 0 then
        units := units.modify (units.size - 1) fun (k, is) => (k, is.push i)
  let all := units.toList.map fun (k, is) => (k, is.toList)
  -- Each after what it uses, in the order written where that does not say.
  let rec visit (fuel : Nat) (done : List String) (k : String) : List String :=
    match fuel with
    | 0 => done
    | fuel + 1 =>
      if done.contains k then done
      else
        let deps := (uses.lookup k).getD []
        let done := deps.foldl (visit fuel) done
        if done.contains k then done else done ++ [k]
  let order := (all.map (·.1)).foldl (visit (all.length + 1)) []
  pure (first, order.filterMap fun k => (all.lookup k).map (k, ·))

/-- The items without the marks of units. -/
def withoutUnitMarks (items : List Syntax.Item) : List Syntax.Item :=
  items.filter fun
    | .fieldNames m [_] [] => m != Syntax.unitMark
    | _ => true

/-- The prelude, with the standard library if `std`, checked: how many items
it is, and what the checker knows after it. A program that declares no name
the prelude has is checked from there, against what the prelude declares.
`drop`: for a program in which some type has `Drop`, checked so that a
function is given how to destroy the types it is generic in. -/
def checkFirstPart (std drop : Bool) : Except String (Nat × Check.St) := do
  if !std then
    let (prelude, _) ← readPrelude.get
    let resolved ← Syntax.Modules.resolve prelude []
    let all := withoutUnitMarks (Syntax.fillDefaults (← Syntax.expandAliases resolved.items))
    return (all.length, ← Check.checkFirst all resolved.info drop)
  let (prelude, items) ← parseProgram "// std" []
  let resolved ← Syntax.Modules.resolve prelude items
  -- (Its modules in the order a program has them, marks and all, so that
  -- what a program has first is these, item for item.)
  let (first, units) := unitsOf resolved.items resolved.info.unitUses
  let items := first ++ units.flatMap (fun (k, is) => Syntax.Item.fieldNames Syntax.unitMark [k] [] :: is)
  let all := Syntax.fillDefaults (← Syntax.expandAliases items)
  -- (Without the first module's mark, at the end: it has nothing.)
  let all := match all.getLast? with
    | some (.fieldNames m [""] []) => if m == Syntax.unitMark then all.dropLast else all
    | _ => all
  pure (all.length, ← Check.checkFirst (withoutUnitMarks all) resolved.info drop)

/-- Each of those, checked once in a process. -/
def checkedPrelude : Thunk (Except String (Nat × Check.St)) := Thunk.mk fun _ => checkFirstPart false false
def checkedStd : Thunk (Except String (Nat × Check.St)) := Thunk.mk fun _ => checkFirstPart true false
def checkedPreludeDrop : Thunk (Except String (Nat × Check.St)) := Thunk.mk fun _ => checkFirstPart false true
def checkedStdDrop : Thunk (Except String (Nat × Check.St)) := Thunk.mk fun _ => checkFirstPart true true

/-- Does some type of a program have `Drop`? -/
partial def hasDrop : List Syntax.Item → Bool
  | [] => false
  | .pub _ i :: rest => hasDrop (i :: rest)
  | .module _ (some body) :: rest => hasDrop body || hasDrop rest
  | .impl _ tr _ _ _ _ :: rest => (tr.splitOn "::").getLast! == "Drop" || hasDrop rest
  | _ :: rest => hasDrop rest

/-- A checked program without what only the checker knows of: its traits (the
checker said how each bound is met, and each is a value passed where it is
needed); its borrows of fields (each the variable's reference, narrowed);
its families of effects (each instance used an effect of its own); and, where
an implementation given to a function is known, the function written out for
it with its trait's functions called by name. `written` has the declarations
with their lifetimes, `all` is without them. -/
def lowered (b : Elab.Blocks) (written all : List Syntax.Item) :
    Except String (List Syntax.Item × Elab.Blocks) := do
  let (items, b) := Elab.untrait b all
  let items ← Elab.unfield b items
  let items ← Elab.instances b written items
  let (items, copies) := Elab.specialize b.traits items
  let items := Elab.foldConstants items
  let b := { b with envFns := b.envFns ++ copies.filterMap fun (name, fn) =>
    (b.envFns.lookup fn).map fun groups => (name, groups) }
  pure (items, b)

/-- Parse, check and elaborate a program together with the prelude, and have the
proved Core type checker accept the result. With `check := false` both checks
are skipped, so that programs which go wrong can still be run. -/
partial def compileSourceAt (src : String) (check : Bool := true)
    (files : List (List String × String) := []) (few : Bool := false)
    (known : List ((String × Nat) × Nat) := []) (packs : Nat := 0) (kept : List Typing.Cert := [])
    (checkKept : Check.Kept := []) (refPats : List (Nat × Bool × List Nat) := [])
    (dotPicks : List (Nat × String) := []) (search : Bool := true) (memo : Infer.Memo := {})
    (firsts : List ((Bool × Bool) × (Nat × Check.St)) := [])
    (lexed : List (List String × Array Syntax.Token) := []) : Except String Compiled := do
  let (prelude, items) ← Trace.timed "parse" fun _ => parseProgram src files check few packs lexed
  -- (Clauses the checker found matching a reference with patterns of a
  -- value: read with those patterns written `&Pattern`.)
  let items := refPats.foldl (fun items (id, uniq, which) => Elab.refPatsItems id uniq which items) items
  -- (Dot calls the checker found are of a type's own function.)
  let items := dotPicks.foldl (fun items (call, fn) => Elab.dotOwnItems call fn items) items
  -- Every name is given its meaning: the modules become one list of items,
  -- each module a unit, after those it uses.
  let resolved ← Trace.timed "resolve names" fun _ => Syntax.Modules.resolve prelude items
  let (firstItems, unitItems) := unitsOf resolved.items resolved.info.unitUses
  let resolved := { resolved with items :=
    firstItems ++ unitItems.flatMap (fun (k, is) => Syntax.Item.fieldNames Syntax.unitMark [k] [] :: is) }
  -- How a constructor is named where a value is shown: without its module,
  -- and the two of the prelude's text under names that mark them.
  let shownName := fun (name : String) =>
    match resolved.info.text with
    | some (textEnd, textChar) =>
      if name == textEnd then Syntax.textEndName
      else if name == textChar then Syntax.textCharName
      else Syntax.lastSegment name
    | none => Syntax.lastSegment name
  -- A type alias is written out wherever it is used.
  let all ← Trace.timed "expand aliases" fun _ => Syntax.expandAliases resolved.items
  -- An implementation that does not write a function its trait gives a body
  -- has that body.
  let all := Trace.timed "fill defaults, write out blankets" fun _ => Syntax.fillDefaults all
  -- What the checker learnt about blocks that share an environment. A program
  -- it rejects is elaborated without that.
  -- (Or that has a cleanup, which a resumption given up runs: what destroys
  -- a resumption that is let go is then written.)
  let drops := hasDrop items || (src.splitOn "defer").length > 1
  -- (The library read for this program alone is checked with it.)
  let withStd := usesStd src files && (src.splitOn "#![no_std]").length == 1
    && !(few && (neededStd (src :: files.map (·.2))).isSome)
  -- (Taken from what an earlier process kept, where it is given.)
  let keptFirst := firsts.lookup (withStd, drops)
  let first : Except String (Nat × Check.St) := match keptFirst, withStd, drops with
    | some f, _, _ => .ok f
    | none, true, false => checkedStd.get
    | none, true, true => checkedStdDrop.get
    | none, false, false => checkedPrelude.get
    | none, false, true => checkedPreludeDrop.get
  -- (What a later process can take instead of checking it again.)
  let firstMade := match keptFirst, first with
    | none, .ok f => some ((withStd, drops), f)
    | _, _ => none
  -- (The library's modules read for this program alone: without what it
  -- cannot reach.)
  let all := match first with
    | .ok (count, _) => if few && check then all.take count ++ withoutUnreached (all.drop count) else all
    | .error _ => all
  -- (The program's own tuple variables whose fields are borrowed apart: a
  -- variable per field. The library, checked once for every program, is as
  -- it was checked.)
  let all := match first with
    | .ok (count, _) => all.take count ++ Elab.splitFieldItems all (all.drop count)
    | .error _ => Elab.splitFieldItems all all
  -- (`kept`: what an earlier check of the same program kept, in the same
  -- process: the steps whose inputs did not change are not checked again.)
  let seed := mixHash (hash withStd) (mixHash (hash drops) (hash few))
  -- (Each unit's items, in order, for the checker; and the items whole.)
  let unitList := match first with
    | .ok (count, _) => (unitsOf (all.drop count) resolved.info.unitUses).2
    | .error _ => []
  let units := unitList.map (fun (u : String × List Syntax.Item) => u.2)
  -- (For each, the units before it that it uses.)
  let unitDeps := unitList.zipIdx.map fun ((k, _), i) =>
    let uses := (resolved.info.unitUses.lookup k).getD []
    ((unitList.take i).zipIdx.filter fun ((k', _), _) => uses.contains k').map (·.2)
  -- (The library's modules among them, which come first.)
  let library := (unitList.takeWhile fun (k, _) => k == "std" || k.startsWith "std::").length
  let infoKeys := unitList.zipIdx.map fun ((k, is), i) =>
    unitInfoKey resolved.info ((unitList.take i).map (·.1)) k is
  -- (And what the prelude and library checked first count, without marks.)
  let first := first.map fun (count, st) => ((withoutUnitMarks (all.take count)).length, st)
  let all := withoutUnitMarks all
  -- (Each unit's items as the items now are: read again after the checker
  -- asked for something to be written otherwise, each has as many items.)
  let cut := fun (rest : List Syntax.Item) =>
    if (units.map List.length).sum == rest.length then
      ((units.foldl (fun (acc : List (List Syntax.Item) × List Syntax.Item) (u : List Syntax.Item) =>
        (acc.1 ++ [acc.2.take u.length], acc.2.drop u.length)) ([], rest)).1).zip infoKeys
    else [(rest, hash resolved.info)]
  let checkOnce := fun (all : List Syntax.Item) =>
    match check, resolved.info.shadowed, first with
    | true, false, .ok (count, first) =>
      Check.checkUnitsKept first (cut (all.drop count)) resolved.info (mixHash seed (hash count)) checkKept
        (library := if (units.map List.length).sum == (all.drop count).length then library else 0)
        (deps := if (units.map List.length).sum == (all.drop count).length then unitDeps else [])
    -- (A program that declares a name the prelude has: the prelude checked
    -- with it, as the first unit, and nothing taken as the program's own.)
    | true, true, .ok (count, _) =>
      Check.checkUnitsKept { dropMode := drops } ((all.take count, hash resolved.info.text) :: cut (all.drop count))
        resolved.info (mixHash seed 77) checkKept (own := false)
    | _, _, _ => (Check.checkProgram all resolved.info drops).map (·, [], [])
  -- (`..` in a tuple pattern: the checker says how many parts it stands
  -- for, and the program is read again with them written.)
  -- (A value used on one path and not on another, bound by `let`: kept in a
  -- variable, as `let mut` keeps it, and the program read again. If that is
  -- refused, what is said is why the value could not be left unused.)
  let rec checkWith (fuel : Nat) (all : List Syntax.Item) (first : Option String) :
      List Syntax.Item × Except String (Elab.Blocks × Check.Kept × Check.Kept) :=
    match checkOnce all with
    | .ok blocks => (all, .ok blocks)
    | .error e =>
      let said := Elab.withoutLetMut ((first.filter fun _ => (Elab.letMutFound e).isNone).getD e)
      match fuel, Elab.restFound e, Elab.letMutFound e with
      | fuel + 1, some (id, count), _ => checkWith fuel (Elab.restItems id count all) first
      | fuel + 1, none, some (owner, line, col, x) =>
        match Elab.letMutItems owner line col x all with
        | (all, true) => checkWith fuel all (some (first.getD e))
        | _ => (all, .error said)
      | _, _, _ => (all, .error said)
  let (all, checked) := Trace.timed "check" fun _ => checkWith 64 all none
  -- (Dot calls the checker chose a type's own function for, by the value's
  -- type: written so for what follows.)
  let all := match checked with
    | .ok (blocks, _) => Elab.argsChosenItems blocks.argsChosen (Elab.chosenItems blocks.dotChosen all)
    | .error _ => all
  let (blocks, checkMade, libraryMade) ← match checked with
    | .ok (blocks, made, shared) => pure (some blocks, made, shared)
    | .error e =>
      let clean := fun (e : String) => Elab.withoutDotOwn (Elab.withoutRefPats e)
      match Elab.refPatsFound e, Elab.dotOwnFound e with
      | some found, _ =>
        if check && refPats.length < 32 && !refPats.contains found then
          match compileSourceAt src check files few known packs kept checkKept (refPats ++ [found]) dotPicks search memo firsts lexed with
          | .ok c => return c
          | .error e' => throw (clean e')
        else if check then throw (clean e) else pure (none, [], [])
      | none, some found =>
        if check && dotPicks.length < 32 && !dotPicks.contains found then
          match compileSourceAt src check files few known packs kept checkKept refPats (dotPicks ++ [found]) search memo firsts lexed with
          | .ok c => return c
          | .error e' => throw (clean e')
        else if check then throw (clean e) else pure (none, [], [])
      | none, none => if check then throw e else pure (none, [], [])
  -- Lifetimes were the checker's to read; and, of what is declared, the
  -- certificate's.
  let written := all
  let all := Elab.eraseLifetimes all
  -- From here on the program has no traits: the checker said how each bound
  -- is met, and each is now a value passed where it is needed.
  let (all, blocks) ← match blocks with
    | some b => do
      let (items, b) ← Trace.timed "lower traits to values" fun _ => lowered b written all
      pure (items, some b)
    | none => pure (all, none)
  -- What nothing reaches is not part of the program that runs. But what the
  -- program's own functions say is looked at wherever they are: one that
  -- `main` does not reach is elaborated too, for what the elaborator alone
  -- refuses, and then left out.
  let roots := "main" :: ((blocks.map (·.coercions)).getD []).map (·.2)
  if check then
    let named := fun (items : List Syntax.Item) => items.filterMap fun
      | Syntax.Item.fn name _ _ _ _ => some name
      | _ => none
    let own := match first with
      | .ok (count, _) => named (written.drop count)
      | .error _ => []
    let reached := named (Elab.reachable roots all)
    let missing := own.filter (!reached.contains ·)
    unless missing.isEmpty do
      match Elab.elabProgram (Elab.reachable (roots ++ missing) all) blocks with
      | .error e => throw e
      | .ok _ => pure ()
  let all := Elab.reachable roots all
  let declared := Elab.withDeclared written all
  -- (What a compile gives, from what was elaborated and certified.)
  let compiled := fun (out : Elab.Output) (cert : Option Typing.Cert) (lent : Nat)
      (places : List ((String × Nat) × Nat)) (made : Infer.Made) =>
    ({ core := out.program, ctorNames := out.ctorNames.map shownName, fnNames := out.fnNames
       opNames := out.opNames, cert, lent, plain := out.plain, places, checkKept := checkMade
       inferMade := made, firstMade, libraryKept := libraryMade } : Compiled)
  let plain := fun (blocks : Option Elab.Blocks) (failed : List (Bool × Bool)) => do
    let out ← Trace.timed "elaborate" fun _ => Elab.elabProgram all blocks
    -- What is unsafe is outside what Core's rules are about: a program that
    -- calls a foreign function or reads memory at an address has no
    -- certificate.
    let first := List.lookup ("%way", 0) known
    let (cert, way, made) ← if check && !out.foreign then
        match Trace.timed "certify" fun _ => certifyProgram declared out.program out.envSizes failed first kept memo with
        | .ok (cert, way, made) => pure (some cert, way, made)
        | .error e =>
          throw s!"the checker accepted this program, but its Core could not be shown to be well typed: {withFnNames out.fnNames e}. This is a defect in the compiler"
      else pure (none, none, {})
    -- (And the way that passed, under a name no function has.)
    let way := match way with
      | some k => [(("%way", 0), k)]
      | none => []
    pure (compiled out cert 0 (way ++ (placeKeys out.siteOwners).toList.map (fun k => (k, 0))) made)
  -- A borrow given a name, or written as an argument of a call of a function,
  -- is a scope of its own in Core if the program can then be shown to follow
  -- every rule. Where it cannot, the borrow is the reference it borrows, as in
  -- a program that is not checked: first every place is tried with the
  -- narrower scope, then each as it passes alone.
  -- (Whether the program can be shown at all with callables taken to bind the
  -- regions of the references they are given, before any borrow is a scope:
  -- where it cannot, no borrow made a scope will change that, and that way
  -- is not tried for each.)
  -- (Where it cannot be shown at all, or only with references taken to be to
  -- one of several cells, which a borrow's scope cannot give out, no place
  -- is tried alone.)
  let shownAtAll := fun (blocks : Option Elab.Blocks) (ranked : Bool) =>
    match Trace.timed "elaborate (borrow scopes)" fun _ => Elab.elabProgram all blocks (fun _ => 0) with
    | .ok out =>
      match Trace.timed "certify (borrow scopes)" fun _ =>
          certifyWith kept declared out.program true out.envSizes true true ranked false memo with
      | .ok (_, accepted, _) => some accepted
      | .error _ => none
    | .error _ => none
  let lending := fun (blocks : Option Elab.Blocks) (ways : List Bool) (sites : Nat → Nat) =>
    match Trace.timed "elaborate (borrow scopes)" fun _ => Elab.elabProgram all blocks sites with
    | .ok out =>
      -- As it is, and then with callables taken to bind the regions of the
      -- references they are given: a function lent to by itself needs that.
      ways.findSome? fun ranked =>
        match Trace.timed "certify (borrow scopes)" fun _ =>
            certifyWith kept declared out.program true out.envSizes true true ranked false memo with
        | .ok (cert, accepted, made) =>
          if out.lent != 0 && accepted then
            some (compiled out (some cert) out.lent
              (((placeKeys out.siteOwners).toList.zip (List.range out.sites)).map fun (k, i) => (k, sites i)) made)
          else none
        | .error _ => none
    | .error _ => none
  -- (The places an earlier compile found, without the way that passed.)
  let placesKnown := known.filter fun (k, _) => k.1 != "%way"
  let build := fun (blocks : Option Elab.Blocks) => do
    if check then
      if let .ok out := Elab.elabProgram all blocks (fun _ => 1) then
        if out.lent != 0 && !out.foreign then
          -- What an earlier compile found for each place is asked first, all
          -- at once; a place it did not see is asked alone first.
          -- (Not looked for one by one: what an earlier compile found, all
          -- at once, and else none.)
          unless search do
            unless placesKnown.isEmpty do
              let guess := (placeKeys out.siteOwners).toList.map fun k => List.lookup k known
              let choice := fun (j : Nat) => match guess[j]? with
                | some (some v) => v
                | _ => 0
              if let some c := lending blocks [false, true] choice then return c
            return ← plain blocks []
          unless placesKnown.isEmpty do
            let guess := (placeKeys out.siteOwners).toList.map fun k => List.lookup k known
            let fresh := (List.range out.sites).filter fun i => (guess[i]?.join).isNone
            let alone := (fresh.map fun i => Task.spawn fun _ =>
              if (lending blocks [false, true] (fun j => if j == i then 1 else 0)).isSome then (i, 1)
              else if !out.twoWays.contains i then (i, 0)
              else (i, ([2, 3, 4].find? fun m =>
                (lending blocks [false, true] (fun j => if j == i then m else 0)).isSome).getD 0)).map Task.get
            let choice := fun (j : Nat) => match guess[j]? with
              | some (some v) => v
              | _ => (List.lookup j alone).getD 0
            if (List.range out.sites).all (choice · == 0) then return ← plain blocks []
            if let some c := lending blocks [false, true] choice then return c
          if let some c := lending blocks [false, true] (fun _ => 1) then return c
          let ranked := shownAtAll blocks true
          let plainly := shownAtAll blocks false
          unless ranked == some true || plainly == some true do
            -- (Those two ways are not tried again for the plain program.)
            return ← plain blocks [(true, false), (false, false)]
          let ways := if ranked.isSome then [false, true] else [false]
          -- First, from every place at once, the places that what fails is
          -- in are taken out, one round at a time: what fails names a
          -- function, and the place it was made for, or every place of the
          -- function it is. Then each place taken out is tried back.
          let blame : List Nat → Sum Compiled (List Nat) := fun choice =>
            match Elab.elabProgram all blocks (fun j => choice[j]?.getD 0) with
            | .error _ => Sum.inr []
            | .ok o =>
              let outcomes : List (Sum Compiled (List Nat)) := ways.map fun ranked =>
                match Trace.timed "certify (borrow scopes)" fun _ =>
                    certifyWith kept declared o.program true o.envSizes true true ranked false memo with
                | .ok (cert, accepted, made) =>
                  if o.lent != 0 && accepted then
                    Sum.inl (compiled o (some cert) o.lent
                      (((placeKeys o.siteOwners).toList.zip (List.range o.sites)).map
                        fun ((k : String × Nat), (i : Nat)) => (k, choice[i]?.getD 0)) made)
                  else Sum.inr (cert.sigs.filterMap fun (e : Typing.SigEntry) =>
                    match o.program.fns[e.fn]? with
                    | some F => if Typing.checkFn cert e F then none else some e.fn
                    | none => none)
                | .error e => Sum.inr (named e)
              match outcomes.find? Sum.isLeft with
              | some found => found
              | none =>
                let fns := outcomes.flatMap fun (x : Sum Compiled (List Nat)) => match x with
                  | .inr fs => fs
                  | .inl _ => []
                -- (The places a function was made for, or those of the
                -- function it is.)
                Sum.inr (fns.eraseDups.flatMap fun f =>
                  match o.fnSites[f]?.join with
                  | some site => [site]
                  | none =>
                    -- (A function made in another is named `.. in `f``.)
                    let described := o.fnNames[f]?.getD ""
                    let name := match (described.splitOn " in `").getLast? with
                      | some last => if (described.splitOn " in `").length > 1
                          then (last.splitOn "`").headD last else described
                      | none => described
                    (List.range o.sites).filter fun j => o.siteOwners[j]? == some name)
          let rec narrow (fuel : Nat) (choice : List Nat) : Option (Compiled × List Nat) :=
            match fuel with
            | 0 => none
            | fuel + 1 =>
              match blame choice with
              | .inl c => some (c, choice)
              | .inr sites =>
                let next := (List.range choice.length).map fun j =>
                  if sites.contains j then 0 else choice[j]?.getD 0
                if next == choice then none else narrow fuel next
          if let some (c, choice) := narrow 24 (List.replicate out.sites 1) then
            let rec back (best : Compiled) (choice : List Nat) : List Nat → Compiled
              | [] => best
              | j :: rest =>
                let tried := choice.set j 1
                match blame tried with
                | .inl c => back c tried rest
                | .inr _ => back best choice rest
            -- (Each taken out is tried back alone, side by side; those that
            -- pass, together; and if that fails, one at a time.)
            let out_ := (List.range choice.length).filter fun j => choice[j]?.getD 0 == 0
            let alone : List (Nat × Bool) :=
              (out_.map fun j => Task.spawn fun _ => (j, (blame (choice.set j 1)).isLeft)).map Task.get
            let passing := alone.filterMap fun (p : Nat × Bool) => if p.2 then some p.1 else none
            if passing.isEmpty then return c
            let together := passing.foldl (fun (ch : List Nat) j => ch.set j 1) choice
            if let .inl c := blame together then return c
            return back c choice passing
          let lending := lending blocks ways
          if out.sites ≤ 160 then
            -- How each place fares alone, trying the narrower scope first.
            -- (Each is asked apart from the others, so all are asked side
            -- by side: the answers are what they would be one at a time.)
            let try_ := fun (i : Nat) =>
              if (lending (fun j => if j == i then 1 else 0)).isSome then 1
              -- (The second way, where the place has one; then the third,
              -- with one of the borrows lasting longer, the first or the
              -- second.)
              else if !out.twoWays.contains i then 0
              else ([2, 3, 4].find? fun m => (lending (fun j => if j == i then m else 0)).isSome).getD 0
            -- A call inside a statement is asked only if the statement's
            -- own place fails: where that passes, the call's borrows are
            -- the statement's.
            -- Where there are many places, they are first asked a run of
            -- them at a time: few fail, and a run that passes whole needs
            -- no place of it asked alone. (Places are numbered in the order
            -- they are written, so a run is mostly one function's.)
            let size := if out.sites ≤ 16 then 1 else (out.sites + 7) / 8
            let whole : List (Task Bool) :=
              if size == 1 then []
              else (List.range ((out.sites + size - 1) / size)).map fun g => Task.spawn fun _ =>
                (lending (fun j => if j / size == g then 1 else 0)).isSome
            let whole := whole.map Task.get
            let passed := fun (i : Nat) => size != 1 && whole[i / size]?.getD false
            -- Where no run passes, a few places spread among them are asked
            -- alone first: if none of those passes either, what fails is not
            -- some few places, and the rest are not asked.
            let hopeless :=
              if size == 1 || whole.any id then false
              else
                let sample := ((List.range 12).map fun k => (k * out.sites) / 12).eraseDups
                let asked := sample.map fun i => Task.spawn fun _ => try_ i
                (asked.map Task.get).all (· == 0)
            if hopeless then return ← plain blocks []
            let first : List (Task Nat) := (List.range out.sites).map fun i => Task.spawn fun _ =>
              if passed i then 1 else if (out.under.lookup i).isSome then 0 else try_ i
            let first := first.map Task.get
            let second : List (Task Nat) := (List.range out.sites).map fun i => Task.spawn fun _ =>
              if passed i then 1
              else match out.under.lookup i with
              | some stmt => if first[stmt]?.getD 0 == 0 then try_ i else 0
              | none => first[i]?.getD 0
            let alone : List Nat := second.map Task.get
            if alone.any (· != 0) then
              if let some c := lending (fun j => alone[j]?.getD 0) then return c
              -- Not all at once: keep each that passes with those kept
              -- before it. A run of them is asked whole first, and by halves
              -- where it fails, so that the few that fail are found without
              -- every place being asked for.
              -- (While a run is asked, so is its first half with what is
              -- kept: the answer wanted next if the run fails.)
              let with_ := fun (kept : List Nat) (coming : List Nat) =>
                coming.foldl (fun (k : List Nat) (i : Nat) => k.set i (alone[i]?.getD 0)) kept
              let ask : List Nat → Task (Option Compiled) := fun next =>
                Task.spawn fun _ => lending (fun j => next[j]?.getD 0)
              let rec add (fuel : Nat) (kept : List Nat) (coming : List Nat) (best : Option Compiled)
                  (whole : Task (Option Compiled)) : List Nat × Option Compiled :=
                match fuel, coming with
                | 0, _ => (kept, best)
                | _, [] => (kept, best)
                | _, [i] =>
                  match Task.get whole with
                  | some c => (with_ kept [i], some c)
                  | none => (kept, best)
                | fuel + 1, _ =>
                  let (a, b) := coming.splitAt (coming.length / 2)
                  let half := ask (with_ kept a)
                  match Task.get whole with
                  | some c => (with_ kept coming, some c)
                  | none =>
                    let (kept, best) := add fuel kept a best half
                    add fuel kept b best (ask (with_ kept b))
              let coming := (List.range out.sites).filter fun i => alone[i]?.getD 0 != 0
              -- (All of them at once has just failed.)
              if let some c := (add out.sites (List.replicate out.sites 0) coming none
                  (Task.spawn fun _ => none)).2 then return c
    plain blocks []
  -- Blocks can share an environment only where a type can state it. Where one
  -- cannot, as when what a block is given may also be a function that is not a
  -- block, every block captures for itself, as it would without the sharing.
  match build blocks with
  | .ok c => pure c
  | .error e =>
    match blocks with
    | some b => if b.links.isEmpty then throw e else build (some { b with links := [] })
    | none => throw e

/-- How many parts the first parentheses of a written type have at their top. -/
def partsWritten (ty : List Char) : Nat :=
  let inner := (ty.dropWhile (· != '(')).drop 1
  let rec count (cs : List Char) (depth parts : Nat) : Nat :=
    match cs with
    | [] => parts
    | c :: rest =>
      if c == '(' || c == '<' || c == '[' then count rest (depth + 1) parts
      else if c == ')' || c == '>' || c == ']' then
        if depth == 0 then parts else count rest (depth - 1) parts
      else if c == ',' && depth == 0 then count rest depth (parts + 1)
      else count rest depth parts
  if inner.isEmpty then 0 else count inner 0 1

/-- How long a list of types an error says is missing an implementation may
need: the parts of the type, and of the tuple the trait is given, together
(one made by joining two is as long as both). -/
def longestUnimplemented (e : String) : Nat :=
  ((e.splitOn "` does not implement `").zip ((e.splitOn "` does not implement `").drop 1)).foldl
    (fun most (before, after) =>
      let ty := ((before.splitOn "`").getLastD "").toList
      let trait := ((after.splitOn "`").headD "").toList
      max most (partsWritten ty + partsWritten (trait.dropWhile (· != '<'))))
    0

/-- Compile a program. A list of types (`impl<..T>`) stands for a list of
any length: it is written out, first, to the longest list the program's
texts write; where the checker then finds a longer tuple or list of
parameters with no implementation, as one made by joining two, the program
is read again with lists that long. -/
def compileSource (src : String) (check : Bool := true)
    (files : List (List String × String) := []) (few : Bool := false)
    (known : List ((String × Nat) × Nat) := []) (kept : List Typing.Cert := [])
    (checkKept : Check.Kept := []) (search : Bool := true) (memo : Infer.Memo := {})
    (firsts : List ((Bool × Bool) × (Nat × Check.St)) := []) : Except String Compiled := do
  -- (What the default prelude has from the library, where the text uses it;
  -- and each text lexed, once.)
  let src := src ++ stdPreludeUses src
  let lexed ← Trace.timed "lex" fun _ => lexTexts src files
  let packs := longestOf lexed
  -- (An implementation over several lists, as one that joins two, is
  -- written out to as many times as long: what it makes can be that long.)
  let lists := ((src :: files.map (·.2)).flatMap fun text =>
    ((text.splitOn "impl<").drop 1).map fun after =>
      (((after.takeWhile (· != '>')).toString.splitOn "..").length - 1)).foldl max 0
  let packs := packs * max 1 lists
  -- (Only a program that has such an implementation is read again.)
  let lists := lists != 0
  let rec go (fuel packs : Nat) : Except String Compiled :=
    match compileSourceAt src check files few known packs kept checkKept (search := search) (memo := memo)
        (firsts := firsts) (lexed := lexed) with
    | .error e =>
      let wanted := longestUnimplemented e
      match fuel with
      | fuel + 1 => if lists && wanted > packs then go fuel (max wanted (2 * packs)) else .error e
      | 0 => .error e
    | .ok c => .ok c
  go 8 packs

/-- Whether a program's Core was shown to follow the ownership rules: `some true`
if so, `some false` if it was only shown to be well typed, `none` if it does not compile. -/
def owned (src : String) : Option Bool :=
  match compileSource src with
  | .ok c => c.cert.map (·.strict)
  | .error _ => none

/-- Whether a program's Core was shown to follow the region rules, likewise. -/
def borrowChecked (src : String) : Option Bool :=
  match compileSource src with
  | .ok c => c.cert.map (·.regions)
  | .error _ => none

/-- How many of a program's borrows are scopes of their own in its Core, which
was then shown to follow the rules for borrows: `none` if the program does not
compile or its Core was not shown to follow them. -/
def lentBorrows (src : String) : Option Nat :=
  match compileSource src with
  | .ok c => if (c.cert.map (·.loans)).getD false then some c.lent else none
  | .error _ => none

/-- The borrows of a program that nothing is proved about: those that are not
scopes of their own in its Core, or every one if the Core was not shown to
follow the rules for borrows. `none` if the program does not compile. A program
for which this is empty has every borrow covered by `checked_exclusive_safety`. -/
def unprovedBorrows (src : String) : Option (List Elab.Borrow) :=
  match compileSource src with
  | .ok c =>
    -- Where the rules were not shown to hold no borrow is a scope, and `plain`
    -- lists every one.
    some c.plain
  | .error _ => none

/-- How many functions the elaborator made for a program's borrows: one for a
borrow that is given a name, and one for each borrow but the last among the
arguments of a call. A call with one borrow needs none. -/
def borrowFns (src : String) : Option Nat :=
  match compileSource src with
  | .ok c => some (c.fnNames.toList.filter fun n => (n.splitOn "borrow").length > 1).length
  | .error _ => none

/-- The characters of a text, if the value is one: the prelude's `Str`, whose
constructors are shown under names no program can write. -/
partial def textOf (names : Array String) : Value → Option (List Nat)
  | .data tag [] => if names[tag]? == some Syntax.textEndName then some [] else none
  | .data tag [.int c, rest] =>
    if names[tag]? == some Syntax.textCharName then (textOf names rest).map (c.toNat :: ·) else none
  | _ => none

/-- Characters as a string; a code that is no character is U+FFFD. -/
def textString (codes : List Nat) : String :=
  String.ofList (codes.map fun c =>
    if c < 0xD800 || (0xE000 ≤ c && c ≤ 0x10FFFF) then Char.ofNat c else Char.ofNat 0xFFFD)

/-- A text inside another value: in quotes. -/
def quoted (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
      else String.singleton c)) "" ++ "\""

partial def showInner (names : Array String) : Value → String
  | .int n => toString n
  | .data tag fields =>
    match textOf names (.data tag fields) with
    | some codes => quoted (textString codes)
    | none =>
      let args := ", ".intercalate (fields.map (showInner names))
      if tag == 0 then s!"({args})"
      else if arrayBase ≤ tag then s!"[{args}]"
      else
        let name := names[tag]?.getD s!"#{tag}"
        if fields.isEmpty then name else s!"{name}({args})"
  | .clo fn _ => s!"<fn {fn}>"
  | .cont id => s!"<resumption {id}>"
  | .label id => s!"<label {id}>"
  | .ref addr _ _ => s!"<ref {addr}>"

/-- A value as it is shown. A text is shown as its characters; inside another
value, in quotes. -/
def showValue (names : Array String) (v : Value) : String :=
  match textOf names v with
  | some codes => textString codes
  | none => showInner names v

/-- Everything the program wrote, one value per line, then its result. -/
def showResult (names : Array String) (r : Result) : String :=
  "\n".intercalate (r.world.output.map (showValue names) ++ [showValue names r.value])

def showOutcome {σ : Type} (names : Array String) : Step σ Result → String
  | .halt r => showResult names r
  | .stuck => "went wrong"
  | .next _ => "out of fuel"

/-- Run a compiled program on both machines with the given input: what it
wrote followed by its value, or what went wrong; both, if they disagree. -/
def evalCompiled (c : Compiled) (input : List Int := []) (fuel : Nat := 200000) : String :=
  let bytecode := compile c.core
  let onCore := showOutcome c.ctorNames
    (Machine.exec (Core.stepIO c.core) fuel (Core.initIO c.core input))
  let onVm := showOutcome c.ctorNames
    (Machine.exec (Bytecode.stepIO bytecode) (fuel * 20) (Bytecode.initIO bytecode input))
  if onCore == onVm then onVm else s!"MISMATCH: Core gives {onCore}, bytecode gives {onVm}"

/--
Compile a program and run it on both machines with the given input. The result
is what it wrote followed by its value, or a description of what went wrong; if
the machines disagree, both are shown.
-/
def evalSource (src : String) (input : List Int := []) (fuel : Nat := 200000)
    (files : List (List String × String) := []) : String :=
  match compileSource src true files with
  | .error e => s!"error: {e}"
  | .ok c => evalCompiled c input fuel

/-- Why a Core configuration has no next step, in the program's own terms. This
is a diagnosis for the user and is not part of the semantics. -/
def explainStuck (c : Compiled) (cfg : Core.Config) : String :=
  let s := cfg.state
  let shown (vs : List Value) := ", ".intercalate (vs.map (showValue c.ctorNames))
  let fnName (fn : Nat) := c.fnNames[fn]?.getD s!"function {fn}"
  let opName (op : Nat) := c.opNames[op]?.getD s!"operation {op}"
  let unbound := "a local is read that has no value; this is a compiler defect"
  let enter (fn : Nat) (vs : List Value) : String :=
    match c.core.fns[fn]? with
    | none => s!"function {fn} does not exist; this is a compiler defect"
    | some _ => s!"no clause of {fnName fn} matches the arguments ({shown vs})"
  let applied (f : Atom) (args : Option (List Value)) : String :=
    match f.eval s.env, args with
    | some (.clo fn _), some vs => enter fn vs
    | some (.cont _), some [_] =>
      "a resumption is used a second time: it was already resumed or cancelled"
    | some (.cont _), some vs =>
      s!"a resumption takes exactly one argument, but is given {vs.length}"
    | some (.label _), some [_] => "a label is applied after its scope has ended"
    | some (.label _), some vs => s!"a label takes exactly one argument, but is given {vs.length}"
    | some v, some _ => s!"`{showValue c.ctorNames v}` is called, but it is not callable"
    | _, _ => unbound
  let performed (op : Nat) : String :=
    match findHandler Core.Frame.asHandler op s.stack with
    | none => s!"operation `{opName op}` is performed, but no handler for it is installed"
    | some _ => s!"the handler for `{opName op}` could not be entered"
  match s.tm with
  | .ret a =>
    match a.eval s.env with
    | none => unbound
    | some v =>
      match s.stack.dropWhile (fun fr => (Core.Frame.asLabel fr).isSome) with
      | .handler _ h :: _ => enter h.ret [v]
      | _ => "a result could not be delivered"
  | .let_ rhs _ =>
    match rhs with
    | .prim p args =>
      match evalAtoms s.env args with
      | some vs =>
        if vs.all (fun v => match v with | .int _ => true | _ => false) then
          -- Which intrinsic it is, by its place in the bytecode's table.
          let code := (Bytecode.Encode.prim p).headD 0
          let second : Int := match vs with
            | [_, .int b] => b
            | _ => 1
          let first : Int := match vs with
            | .int a :: _ => a
            | _ => 0
          if code ≤ 2 then
            s!"integer overflow: the result of an operation on ({shown vs}) does not fit in 64 bits"
          else if second == 0 && (code == 5 || code == 6 || code == 34 || code == 35) then
            s!"division by zero: ({shown vs})"
          else if code == 7 then
            let kind := if second < 0 then s!"{second.natAbs} bits without a sign" else s!"{second} bits"
            s!"`{first}` does not fit its type, which has {kind}"
          else if code == 39 then
            s!"place `{first}` is asked of something that has {second}"
          else s!"an operation on ({shown vs}) has no result: it would not fit, or there is none"
        else match vs with
          | [.data tag fields, .int i] =>
            if arrayBase ≤ tag then s!"place `{i}` is asked of an array of {fields.length}"
            else s!"an arithmetic intrinsic is applied to ({shown vs})"
          | _ => s!"an arithmetic intrinsic is applied to ({shown vs})"
      | none => unbound
    | .place pl =>
      match s.env[pl.var]? with
      | some v => s!"`{showValue c.ctorNames v}` does not have the field being read"
      | none => unbound
    | _ => unbound
  | .call f args _ => applied f (evalAtoms s.env args)
  | .tail f args => applied f (evalAtoms s.env args)
  | .handle _ _ _ thunk _ => applied thunk (some [])
  | .handleTail _ _ _ thunk => applied thunk (some [])
  | .label thunk _ => applied thunk (some [.label s.store.labels])
  | .labelTail thunk => applied thunk (some [.label s.store.labels])
  | .guard _ thunk _ => applied thunk (some [])
  | .guardTail _ thunk => applied thunk (some [])
  | .raise op _ => performed op
  | .perform op _ _ => performed op
  | .cancel _ _ => "`cancel` is applied to something that is not a usable resumption"
  | .cell _ thunk _ => applied thunk (some [.ref s.store.cells.length 0 []])
  | .cellTail _ thunk => applied thunk (some [.ref s.store.cells.length 0 []])
  | .lend _ r thunk pre post _ =>
    match r.eval s.env with
    | some (.ref a _ path) =>
      applied thunk (do
        pure ((← evalAtoms s.env pre) ++ .ref a (s.store.labels + 1) path
          :: (← evalAtoms s.env post)))
    | some v => s!"`{showValue c.ctorNames v}` is lent, but it is not a reference"
    | none => unbound
  | .mem _ args _ =>
    match evalAtoms s.env args with
    | some (.ref _ _ _ :: _) => "a reference is used after the cell it points to was freed"
    | some vs => s!"a memory operation is applied to ({shown vs}), which is not a reference"
    | none => unbound
  | .host id _ _ =>
    if id ≥ 2 then "a foreign function or memory at an address has no meaning on this machine: build the program and run it on the Rust VM"
    else s!"host operation {id} rejected its arguments"

/-- Run a program on the Core machine and, if it goes wrong, say why. -/
def diagnose (src : String) (input : List Int := []) (fuel : Nat := 200000) : String :=
  match compileSource src (check := false) with
  | .error e => s!"error: {e}"
  | .ok c =>
    let rec go : Nat → Core.Config → String
      | 0, _ => "out of fuel"
      | n + 1, cfg =>
        match Core.stepIO c.core cfg with
        | .next cfg' => go n cfg'
        | .halt _ => "did not go wrong"
        | .stuck => explainStuck c cfg
    go fuel (Core.initIO c.core input)

/-- The deepest the bytecode machine's stack gets while running a program. -/
def peakStack (src : String) (input : List Int := []) (fuel : Nat := 4000000) : Option Nat :=
  match compileSource src with
  | .error _ => none
  | .ok c =>
    let bytecode := compile c.core
    let rec go : Nat → Bytecode.Config → Nat → Option Nat
      | 0, _, _ => none
      | n + 1, cfg, peak =>
        let peak := max peak cfg.state.frames.length
        match Bytecode.stepIO bytecode cfg with
        | .next cfg' => go n cfg' peak
        | .halt _ => some peak
        | .stuck => none
    go fuel (Bytecode.initIO bytecode input) 0

/-- How many memory cells are still live when a program finishes. The step that
ends the program also leaves the scopes still on the stack, so their cells do
not count. -/
def liveCells (src : String) (input : List Int := []) (fuel : Nat := 4000000) : Option Nat :=
  match compileSource src with
  | .error _ => none
  | .ok c =>
    let bytecode := compile c.core
    let rec go : Nat → Bytecode.Config → Option Nat
      | 0, _ => none
      | n + 1, cfg =>
        match Bytecode.stepIO bytecode cfg with
        | .next cfg' => go n cfg'
        | .halt _ =>
          let leaving := cfg.state.frames.filterMap fun
            | .cell a => some a
            | _ => none
          let cells := cfg.state.store.cells
          some ((List.range cells.length).filter fun a =>
            (cells[a]?.getD none).isSome && !leaving.contains a).length
        | .stuck => none
    go fuel (Bytecode.initIO bytecode input)

/-- The cleanups of a finished program: how many guards it installed, how many
cleanups it started, and how many guards were left in resumptions never taken.
`Core.cleanup_accounting` proves the first is the sum of the other two. -/
def cleanupsOf (core : Core.Program) (input : List Int := []) (fuel : Nat := 4000000) :
    Option (Nat × Nat × Nat) :=
  let rec go : Nat → Nat → Nat → Core.Config → Option (Nat × Nat × Nat)
    | 0, _, _, _ => none
    | n + 1, installed, started, cfg =>
      match Core.stepIO core cfg with
      | .next cfg' =>
        go n (installed + Core.installs cfg.state) (started + Core.starts cfg.state) cfg'
      | .halt _ => some (installed, started, Core.held cfg.state.store.conts)
      | .stuck => none
  go fuel 0 0 (Core.initIO core input)

/-- The same, of a program's text. -/
def cleanups (src : String) (input : List Int := []) (fuel : Nat := 4000000) :
    Option (Nat × Nat × Nat) :=
  match compileSource src with
  | .error _ => none
  | .ok c => cleanupsOf c.core input fuel

end Glorious
