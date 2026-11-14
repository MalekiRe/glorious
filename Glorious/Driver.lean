module

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

/-- Find a certificate for a program's Core and have the proved checker accept
it: with the ownership rules and the region rules if the program can be shown
to meet them, and otherwise with those of them it can, or as a typing only.
An error here is a defect in the compiler, not in the program. -/
def certifyProgram (items : List Syntax.Item) (p : Core.Program)
    (envSizes : List (Nat × Nat × Nat) := []) (failed : List (Bool × Bool) := []) :
    Except String Typing.Cert := do
  -- With the region rules, first with callables taken to bind a region
  -- where they are given a reference to a cell, and then without; and only
  -- then with references taken to be to one of several cells where they
  -- have to be.
  let one (strict regions loans ranked widen : Bool) : Option Typing.Cert :=
    match Infer.certify items p strict envSizes regions loans ranked widen with
    | .ok cert => if Typing.checkProgram cert p then some cert else none
    | .error _ => none
  -- (`failed`: ways already seen to fail with every rule, not tried again.)
  let attempt (strict regions loans : Bool) : Option Typing.Cert :=
    (if regions then [(true, false), (false, false), (false, true), (true, true)]
      else [(false, false)]).findSome? fun (ranked, widen) =>
      if strict && regions && loans && failed.contains (ranked, widen) then none
      else one strict regions loans ranked widen
  if let some cert := attempt true true true then return cert
  if let some cert := attempt true true false then return cert
  if let some cert := attempt true false false then return cert
  if let some cert := attempt false true true then return cert
  if let some cert := attempt false true false then return cert
  let cert ← match Infer.certify items p false envSizes with
    | .ok cert => pure cert
    | .error e => throw s!"no certificate was found: {e}"
  if Typing.checkProgram cert p then pure cert
  else throw s!"the certificate was rejected: {Infer.rejected cert p}"

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

/-- The prelude and a program as written: the first module's text, and the
texts of the modules that are files of their own, each with its path. Where
the program says `mod name;` the items of that module's text are put. -/
def parseProgram (src : String) (files : List (List String × String)) (check : Bool := true)
    (few : Bool := false) :
    Except String (List Syntax.Item × List Syntax.Item) := do
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
    let _ ← Syntax.declaredSyntax fix text
    Syntax.textSyntax path text
  let unread ← match read with
    | some _ => pure []
    | none => (if std then library else []).mapM fun (path, text) => do
        let _ ← Syntax.declaredSyntax fix text
        Syntax.textSyntax path text
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
    (fixed := fixed)
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
                  (tables := tables) (path := here) (fixed := fixed && k ≥ (if std then library.length else 0)) with
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

/-- The prelude checked, once: how many items it is, and what the checker
knows after it. A program that declares no name the prelude has is checked
from there, against what the prelude declares. -/
def checkedPrelude : Thunk (Except String (Nat × Check.St)) := Thunk.mk fun _ => do
  let (prelude, _) ← readPrelude.get
  let resolved ← Syntax.Modules.resolve prelude []
  let all := Syntax.fillDefaults (← Syntax.expandAliases resolved.items)
  pure (all.length, ← Check.checkFirst all resolved.info)

/-- The prelude and the standard library checked, once. -/
def checkedStd : Thunk (Except String (Nat × Check.St)) := Thunk.mk fun _ => do
  let (prelude, items) ← parseProgram "// std" []
  let resolved ← Syntax.Modules.resolve prelude items
  let all := Syntax.fillDefaults (← Syntax.expandAliases resolved.items)
  pure (all.length, ← Check.checkFirst all resolved.info)

/-- The same two, for a program in which some type has `Drop`: checked so
that a function is given how to destroy the types it is generic in. -/
def checkedPreludeDrop : Thunk (Except String (Nat × Check.St)) := Thunk.mk fun _ => do
  let (prelude, _) ← readPrelude.get
  let resolved ← Syntax.Modules.resolve prelude []
  let all := Syntax.fillDefaults (← Syntax.expandAliases resolved.items)
  pure (all.length, ← Check.checkFirst all resolved.info true)

def checkedStdDrop : Thunk (Except String (Nat × Check.St)) := Thunk.mk fun _ => do
  let (prelude, items) ← parseProgram "// std" []
  let resolved ← Syntax.Modules.resolve prelude items
  let all := Syntax.fillDefaults (← Syntax.expandAliases resolved.items)
  pure (all.length, ← Check.checkFirst all resolved.info true)

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
def compileSource (src : String) (check : Bool := true)
    (files : List (List String × String) := []) (few : Bool := false) : Except String Compiled := do
  let (prelude, items) ← parseProgram src files check few
  -- Every name is given its meaning: the modules become one list of items.
  let resolved ← Syntax.Modules.resolve prelude items
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
  let all ← Syntax.expandAliases resolved.items
  -- An implementation that does not write a function its trait gives a body
  -- has that body.
  let all := Syntax.fillDefaults all
  -- What the checker learnt about blocks that share an environment. A program
  -- it rejects is elaborated without that.
  let drops := hasDrop items
  -- (The library read for this program alone is checked with it.)
  let withStd := usesStd src files && (src.splitOn "#![no_std]").length == 1
    && !(few && (neededStd (src :: files.map (·.2))).isSome)
  let first := match withStd, drops with
    | true, false => checkedStd.get
    | true, true => checkedStdDrop.get
    | false, false => checkedPrelude.get
    | false, true => checkedPreludeDrop.get
  let checkOnce := fun (all : List Syntax.Item) =>
    match check && !resolved.info.shadowed, first with
    | true, .ok (count, first) => Check.checkAfter first (all.drop count) resolved.info
    | _, _ => Check.checkProgram all resolved.info drops
  -- (`..` in a tuple pattern: the checker says how many parts it stands
  -- for, and the program is read again with them written.)
  let rec checkWith (fuel : Nat) (all : List Syntax.Item) :
      List Syntax.Item × Except String Elab.Blocks :=
    match checkOnce all with
    | .ok blocks => (all, .ok blocks)
    | .error e =>
      match fuel, Elab.restFound e with
      | fuel + 1, some (id, count) => checkWith fuel (Elab.restItems id count all)
      | _, _ => (all, .error e)
  let (all, checked) := checkWith 64 all
  let blocks ← match checked with
    | .ok blocks => pure (some blocks)
    | .error e => if check then throw e else pure none
  -- Lifetimes were the checker's to read; and, of what is declared, the
  -- certificate's.
  let written := all
  let all := Elab.eraseLifetimes all
  -- From here on the program has no traits: the checker said how each bound
  -- is met, and each is now a value passed where it is needed.
  let (all, blocks) ← match blocks with
    | some b => do
      let (items, b) ← lowered b written all
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
  let plain := fun (blocks : Option Elab.Blocks) (failed : List (Bool × Bool)) => do
    let out ← Elab.elabProgram all blocks
    -- What is unsafe is outside what Core's rules are about: a program that
    -- calls a foreign function or reads memory at an address has no
    -- certificate.
    let cert ← if check && !out.foreign then
        match certifyProgram declared out.program out.envSizes failed with
        | .ok cert => pure (some cert)
        | .error e =>
          throw s!"the checker accepted this program, but its Core could not be shown to be well typed: {e}. This is a defect in the compiler"
      else pure none
    pure (⟨out.program, out.ctorNames.map shownName, out.fnNames, out.opNames, cert, 0, out.plain⟩ : Compiled)
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
    match Elab.elabProgram all blocks (fun _ => 0) with
    | .ok out =>
      match Infer.certify declared out.program true out.envSizes true true ranked with
      | .ok cert => some (Typing.checkProgram cert out.program)
      | .error _ => none
    | .error _ => none
  let lending := fun (blocks : Option Elab.Blocks) (ways : List Bool) (sites : Nat → Nat) =>
    match Elab.elabProgram all blocks sites with
    | .ok out =>
      -- As it is, and then with callables taken to bind the regions of the
      -- references they are given: a function lent to by itself needs that.
      ways.findSome? fun ranked =>
        match Infer.certify declared out.program true out.envSizes true true ranked with
        | .ok cert =>
          if out.lent != 0 && Typing.checkProgram cert out.program then
            some (⟨out.program, out.ctorNames.map shownName, out.fnNames, out.opNames, some cert, out.lent,
              out.plain⟩ : Compiled)
          else none
        | .error _ => none
    | .error _ => none
  let build := fun (blocks : Option Elab.Blocks) => do
    if check then
      if let .ok out := Elab.elabProgram all blocks (fun _ => 1) then
        if out.lent != 0 && !out.foreign then
          if let some c := lending blocks [false, true] (fun _ => 1) then return c
          let ranked := shownAtAll blocks true
          let plainly := shownAtAll blocks false
          unless ranked == some true || plainly == some true do
            -- (Those two ways are not tried again for the plain program.)
            return ← plain blocks [(true, false), (false, false)]
          let ways := if ranked.isSome then [false, true] else [false]
          let lending := lending blocks ways
          if out.sites ≤ 160 then
            -- How each place fares alone, trying the narrower scope first.
            -- (Each is asked apart from the others, so all are asked side
            -- by side: the answers are what they would be one at a time.)
            let try_ := fun (i : Nat) =>
              if (lending (fun j => if j == i then 1 else 0)).isSome then 1
              -- (The second way, where the place has one.)
              else if !out.twoWays.contains i then 0
              else if (lending (fun j => if j == i then 2 else 0)).isSome then 2
              else 0
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
        else s!"an arithmetic intrinsic is applied to ({shown vs})"
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
def cleanups (src : String) (input : List Int := []) (fuel : Nat := 4000000) :
    Option (Nat × Nat × Nat) :=
  match compileSource src with
  | .error _ => none
  | .ok c =>
    let rec go : Nat → Nat → Nat → Core.Config → Option (Nat × Nat × Nat)
      | 0, _, _, _ => none
      | n + 1, installed, started, cfg =>
        match Core.stepIO c.core cfg with
        | .next cfg' =>
          go n (installed + Core.installs cfg.state) (started + Core.starts cfg.state) cfg'
        | .halt _ => some (installed, started, Core.held cfg.state.store.conts)
        | .stuck => none
    go fuel 0 0 (Core.initIO c.core input)

end Glorious
