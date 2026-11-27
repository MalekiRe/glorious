module

public import Glorious.Trace
public import Glorious.Syntax.Parser
public import Glorious.Syntax.Resolve
public import Glorious.Syntax.Modules
public import Glorious.Elab
public import Glorious.Elab.Instances
public import Glorious.Elab.Specialize
public import Glorious.Elab.Lower
public import Glorious.Comptime
public import Glorious.Check
public import Glorious.Typer
public import Glorious.Core.Show
public import Glorious.Lower.Typed
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

/-- What is read of a text before any text is parsed: what it declares. -/
structure TextRead where
  said : Syntax.TextSyntax

/-- Texts as an earlier compile read them, under each text and its path
(`textKey`): one that is the same is not lexed again for this. -/
abbrev Texts := Std.HashMap UInt64 TextRead

def textKey (path : List String) (text : String) : UInt64 := mixHash (hash text) (hash path)

structure Compiled where
  /-- What the machines run: `checked` lowered by its types (`Lower.program`),
  where it can be; otherwise `checked` itself. -/
  core : Core.Program
  /-- The Core as elaborated, before it is lowered. -/
  checked : Core.Program := core
  /-- Whether `core` is `checked` lowered. -/
  lowered : Bool := false
  ctorNames : Array String
  fnNames : Array String
  opNames : Array String
  /-- The types of `checked`'s functions (`Typer`): what the typed lowering
  works from. -/
  types : Thunk (Option Lower.Types) := Thunk.pure none
  /-- What the checker kept, for a later compile of the program in the same
  process (`Check.Kept`). -/
  checkKept : Check.Kept := []
  /-- The prelude (and library) as checked, where this compile checked it:
  for a later process, by whether the library is in and whether `Drop` is. -/
  firstMade : Option ((Bool × Bool) × (Nat × Check.St)) := none
  /-- What the checker kept of the library's modules, for any program that
  begins with them. -/
  libraryKept : Check.Kept := []
  /-- What each of the program's own groups added, where `groupsKept` was
  given: for the next compile of the program (`Check.checkGroupKept`). -/
  groupsMade : Array (UInt64 × Check.KeptGroup) := #[]
  /-- Each module's items as name resolution made them, where `unitsKept`
  was given: for the next compile (`Syntax.Modules.UnitsKept`). -/
  unitsMade : List (UInt64 × List Syntax.Item × Syntax.Modules.UnitMade) := []
  /-- What the front end's passes made of each item, where `frontKept` was
  given: for the next compile (`Syntax.Flat.FrontMemo`). -/
  frontMade : Array (UInt64 × List Syntax.Item) := #[]
  /-- Each module's items as this compile parsed them or took them, under
  what they were parsed from: kept for the next. -/
  parsedMade : List (UInt64 × List Syntax.Item) := []
  /-- Each text as this compile read it or took it (`Texts`), for the next. -/
  textsMade : List (UInt64 × TextRead) := []
  /-- Each group of the program's own text's items, where `itemsKept` was
  given: for the next compile (`Syntax.ItemsKept`). -/
  itemsMade : Syntax.ItemsKept := {}
  /-- What elaborating each top-level function made, where `elabKept` was
  given: for the next compile (`Elab.ElabKept`). -/
  elabMade : Elab.ElabMemo := {}
  /-- What lowering each function made: for the next compile (`Elab.LowerKept`). -/
  lowerMade : Elab.LowerMemo := {}
  /-- What lowering each function by its types made (`Lower.TypedMemo`). -/
  typedMade : Lower.TypedMemo := {}

/-- What of a program's modules a unit's check reads besides its own items:
the coercions that apply in it, the dot calls among its calls the resolver
found more than one function for, and which fields of the constructors of it
and of the units before it are `pub`. -/
def unitInfoKey (info : Syntax.ModuleInfo) (before : List String) (unit : String)
    (items : List Syntax.Item) : UInt64 :=
  -- (The calls of its bodies, where they are kept.)
  let ids : Std.HashSet Nat := items.foldl (fun set i =>
    i.allBodies.foldl (fun set b => b.exprs.foldl (fun set n => match n with
      | .call id _ _ | .tailCall id _ _ => set.insert id
      | _ => set) set) set) {}
  let alts := info.dotAlts.filter fun (id, _) => ids.contains id
  let seen := unit :: before
  let vis := info.fieldVis.filter fun (_, home, _) => seen.contains home
  hash (unit, info.coercions.lookup unit, alts, vis, info.text, info.shadowed)

/-- Every name a body writes, bound or not, and every field or function named
after a dot, read off its nodes where they are kept: more than it can mean,
never less. -/
def namesInBody (acc : List String) (b : Syntax.Flat.Body) : List String :=
  b.exprs.foldl (fun acc n => match n with
    | .name _ x | .ref _ x => x :: acc
    | .refField _ _ x path _ => x :: path ++ acc
    | .fieldOf _ _ x => x :: acc
    | _ => acc) acc

/-- The names written in an item that is not one of the library's functions. -/
partial def namesInItem (acc : List String) : Syntax.Item → List String
  | .fn _ _ _ _ b => namesInBody acc b
  | .impl { methods := methods, .. } => methods.foldl namesInItem acc
  | .traitInfo _ _ defaults _ _ => defaults.foldl namesInItem acc
  | .alias _ b _ => namesInBody acc b
  | (.coerce name) => name :: acc
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

/-- What the typer or the lowering said, with each function it names (`function 12`) followed by what that function is. -/
def withFnNames (names : Array String) (e : String) : String :=
  match e.splitOn "function " with
  | [] => e
  | first :: rest => first ++ String.join (rest.map fun after =>
      let digits := (after.takeWhile Char.isDigit).toString
      match digits.toNat? with
      | some n => s!"function {digits} ({(names[n]?).getD "?"})" ++ (after.drop digits.length).toString
      | none => "function " ++ after)

/-- Does `text` have `pat` in it, byte for byte. -/
def hasText (text pat : String) : Bool := Id.run do
  let t := text.toUTF8
  let p := pat.toUTF8
  if p.size == 0 then return true
  if p.size > t.size then return false
  let first := p[0]!
  for i in [0:t.size - p.size + 1] do
    if t[i]! == first then
      let mut ok := true
      for j in [1:p.size] do
        if t[i + j]! != p[j]! then
          ok := false
          break
      if ok then return true
  return false

/-- The modules of the names of the library's prelude a text writes
(`Syntax.Modules.libraryPrelude`) as names of their own, and neither
declares nor brings itself: the program then reads the library, and those.
(What is read, not what a name means: a name the text declares is its own
whatever is read.) One pass over the text's words. -/
def preludeModules (text : String) : List String := Id.run do
  -- (Over the bytes: a word is of ASCII letters, digits and `_`, and the
  -- bytes of any other character are none of those, as the character is
  -- not. Each word made once, from its bytes.)
  let isWord := fun (b : UInt8) => (b ≥ 48 && b ≤ 57) || (b ≥ 65 && b ≤ 90) || (b ≥ 97 && b ≤ 122) || b == 95
  let decls := ["fn", "enum", "struct", "type", "trait", "effect", "const", "let"]
  let bytes := text.toUTF8
  let n := bytes.size
  let mut mentioned : Std.HashSet String := {}
  let mut own : Std.HashSet String := {}
  let mut before : UInt8 := 32
  let mut start := 0
  let mut inWord := false
  let mut afterPath := false
  let mut prev := ""
  let mut inUse := false
  for i in [0:n + 1] do
    let b := if i < n then bytes[i]! else 32
    if isWord b then
      if !inWord then
        inWord := true
        start := i
        afterPath := before == 58 || before == 46
    else
      if inWord then
        inWord := false
        let word := String.fromUTF8! (bytes.extract start i)
        if word == "use" then
          prev := word
          inUse := true
        else
          if inUse || afterPath || decls.contains prev then own := own.insert word
          else mentioned := mentioned.insert word
          prev := word
      if b == 59 then inUse := false
      if b != 32 && b != 10 then before := b
  pure ((Syntax.Modules.libraryPrelude.filter fun (name, _) =>
    mentioned.contains name && !own.contains name).map (·.2)).eraseDups

def mentionsPrelude (text : String) : Bool := !(preludeModules text).isEmpty

/-- Does a program have the standard library: does it name `std`, and have no
module `std` of its own? -/
def usesStd (src : String) (files : List (List String × String)) : Bool :=
  let named := fun (text : String) =>
    hasText text "std" || hasText text "core::" || hasText text "alloc::"
  let own := fun (text : String) =>
    hasText text "mod std {" || hasText text "mod std{"
  (named src || mentionsPrelude src || files.any fun (_, text) => named text || mentionsPrelude text)
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
    if let .impl { trait := tr, head := head, .. } := item then
      let tr := tr.base
      if denied.contains (last tr, last head) then
        throw s!"`{last head}` is said not to have `{last tr}` (`impl !{last tr} for {last head}`), and an implementation says it does"
  for item in all do
    if let .impl { trait := tr, head := head, .. } := item then
      let tr := tr.base
      let said := promised.contains (last tr, last head)
      if traits.contains (last tr) && !said then
        throw s!"`{last tr}` is an `unsafe trait`: its implementation for `{last head}` is written `unsafe impl {last tr} for {last head}`"
      if !traits.contains (last tr) && said then
        throw s!"`unsafe impl {last tr} for {last head}`: `{last tr}` is not an `unsafe trait`"

/-- The prelude read, once. -/
def readPrelude : Thunk (Except String (List Syntax.Item × Syntax.Fixities)) := Thunk.mk fun _ =>
  match Syntax.parse {} Prelude.source (reflect := false) with
  | .ok (items, fix) => .ok (Syntax.textItem :: items, fix)
  | .error e => .error s!"prelude: {e}"

/-- The library's texts read, once: what each says before it is parsed, the
operators of each of its modules in a program that declares none, every
name written in the texts, and each text parsed. A program that names the
library reads them the same, unless it has a constructor with named fields
whose name the library's texts write, or brings an operator into one of the
library's modules: then they are read again for that program. -/
structure StdRead where
  said : List Syntax.TextSyntax
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
        (path := path) (fixed := true) (reflect := false) with
    | .ok (items, _) => parsed := parsed.push items
    | .error e => throw s!"module `{"::".intercalate path}`: {e}"
  let names := syn.foldl (fun set s => s.names.foldl (fun set n => set.insert n) set) {}
  pure { said := syn, names := names, tables := tables, parsed := parsed }

/-- Where a scan for names of the library is (`libraryNames`). -/
structure LibScan where
  word : String := ""
  last : String := ""
  /-- The root the last word was, where only colons came after it. -/
  root : Option String := none
  colons : Nat := 0
  /-- The root whose module the word being read names. -/
  module : Option String := none
  many : Bool := false
  named : List (List String) := []

/-- How a text names the library: whether some way says more than one
module, or all (`std::{a, b}`, `std::*`, `use std;`), and each
`root::module` it writes. One pass over the characters. -/
def libraryNames (text : String) : Bool × List (List String) :=
  let roots := ["std", "core", "alloc"]
  let isWord := fun (c : Char) => c.isAlphanum || c == '_'
  let s := (text.push ' ').foldl (init := ({} : LibScan)) fun s c =>
    if isWord c then
      if s.word.isEmpty then
        { s with word := s.word.push c, module := if s.colons == 2 then s.root else none }
      else { s with word := s.word.push c }
    else
      -- (A word ends.)
      let s := if s.word.isEmpty then s else
        { s with
          named := match s.module with
            | some r => [r, s.word] :: s.named
            | none => s.named
          many := s.many || (c == ';' && s.last == "use" && roots.contains s.word)
          root := if roots.contains s.word then some s.word else none
          last := s.word, word := "", module := none, colons := 0 }
      if c == ':' && s.root.isSome && s.colons < 2 then { s with colons := s.colons + 1 }
      else if s.colons == 2 && (c == '{' || c == '*') then { s with many := true, colons := 0, root := none }
      else { s with colons := 0, root := none }
  (s.many, s.named.reverse)

/-- The library's modules a program needs: those its texts name after
`std::`, `core::` or `alloc::`, and those that these name in turn; with the
texts of the three roots cut down to them. Nothing where the texts name the
library some other way (`use std::{a, b}`), and all of it is then read. -/
def neededStd (texts : List String) : Option (List (List String × String)) :=
  let roots := ["std", "core", "alloc"]
  let scanned := texts.map libraryNames
  if scanned.any (·.1) then none
  else
    let named := fun (text : String) => (libraryNames text).2
    let rec close (fuel : Nat) (have_ todo : List (List String)) : List (List String) :=
      match fuel, todo with
      | 0, _ => have_
      | _, [] => have_
      | fuel + 1, path :: rest =>
        if have_.contains path then close fuel have_ rest
        else match Std.texts.lookup path with
          | some text => close fuel (path :: have_) (named text ++ rest)
          | none => close fuel have_ rest
    -- (The modules of the library's prelude a text writes names of.)
    let prelude := (texts.flatMap preludeModules).eraseDups.map (["std", ·])
    let needed := close 4096 [] (prelude ++ scanned.flatMap (·.2))
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

/-- A text read so: as `kept` has it, or from its tokens. -/
def readText (fix : Syntax.Fixities) (kept : Texts) (path : List String) (text : String)
    (toks : Option (Array Syntax.Token)) : Except String (UInt64 × TextRead) := do
  let key := textKey path text
  if let some r := kept[key]? then return (key, r)
  let toks ← match toks with
    | some t => pure t
    | none => Syntax.lex text
  let _ ← Syntax.declaredSyntax fix text toks
  pure (key, ⟨← Syntax.textSyntax path text toks⟩)

/-- Modules' items as an earlier compile parsed them, under what each was
parsed from (`parseKey`). -/
abbrev Parsed := Std.HashMap UInt64 (List Syntax.Item)

/-- What a module's items are parsed from: its text, where its callables are
numbered from, the constructors with named fields, its operators, its path,
and whether arrays have lengths. (The prelude's operators are this
compiler's, as is what keeps it.) -/
def parseKey (text : String) (base : Nat) (records : List String)
    (tables : List (List String × Syntax.Fixities)) (path : List String) (fixed : Bool)
    (reflect : Bool := false) :
    UInt64 :=
  let fix := (tables.lookup path).map fun f =>
    (f.infixes.map (fun (o, p, a) => (o, p, match a with
      | .left => (0 : Nat)
      | .right => 1
      | .non => 2)), f.prefixes, f.bound)
  mixHash (hash text) (hash (base, records, fix, path, fixed, reflect))

/-- Does a text name reflection, `std::reflect`, through which alone
anything asks a type's `Reflect`. -/
def mentionsReflection (text : String) : Bool := hasText text "std::reflect"

/-- The prelude and a program as written: the first module's text, and the
texts of the modules that are files of their own, each with its path. Where
the program says `mod name;` the items of that module's text are put. -/
def parseProgram (src : String) (files : List (List String × String)) (check : Bool := true)
    (few : Bool := false) (lexed : List (List String × Array Syntax.Token) := [])
    (parsedKept : Parsed := {}) (preludeKept : Option (List Syntax.Item × Syntax.Fixities) := none)
    (texts : Texts := {}) (itemsKept : Option Syntax.ItemsKept := none) :
    Except String (List Syntax.Item × List Syntax.Item × List (UInt64 × List Syntax.Item) × List (UInt64 × TextRead)
      × Syntax.ItemsKept) := do
  -- (The program's own texts lexed once, where they were not already.)
  let lexed ← if !lexed.isEmpty then pure lexed else lexTexts src files
  let tokensOf := fun (path : List String) => lexed.lookup path
  -- The library's texts are files of the program, before its own.
  -- (`#![no_std]`: without the library, whatever the text mentions.)
  let std := usesStd src files && !hasText src "#![no_std]"
  let own := files
  -- (`few`: only the library's modules the program needs, read and checked
  -- with it, where it is one program that is compiled: the whole library
  -- read once serves many.)
  let needed := if few && std then neededStd (src :: own.map (·.2)) else none
  let library := needed.getD Std.texts
  let files := if std then library ++ files else files
  -- (The prelude as an earlier process of this compiler parsed it, where
  -- one did: `preludeKept`.)
  let (prelude, fix) ← Trace.timed "parse: the prelude" fun _ => if check then (match preludeKept with | some p => pure p | none => readPrelude.get) else
    match Syntax.parse {} Prelude.unchecked (reflect := false) with
    | .ok (items, fix) => pure (Syntax.textItem :: items, fix)
    | .error e => throw s!"prelude: {e}"
  -- The library's texts as they were read once, where the program names it.
  let read ← if std && check && needed.isNone then
      (do pure (some (← readStd.get)) : Except String (Option StdRead))
    else pure none
  -- Operators and the constructors with named fields are known to every
  -- text, whichever declares them.
  let ownRead ← Trace.timed "parse: what each text declares" fun _ => (([], src) :: own).mapM fun (path, text) =>
    readText fix texts path text (tokensOf path)
  let said := ownRead.map (·.2.said)
  let unread ← Trace.timed "parse: what the library declares" fun _ => match read with
    | some _ => pure []
    | none => (if std then library else []).mapM fun (path, text) => readText fix texts path text (stdTokens path text)
  let librarySaid := match read with
    | some r => r.said
    | none => unread.map (·.2.said)
  let ordered := said.take 1 ++ librarySaid ++ said.drop 1
  let records := ordered.flatMap (·.records)
  -- An operator's fixity is its module's.
  let tables ← Syntax.joinFixities fix ordered
  -- The library as it was read once is the library as this program reads
  -- it, if none of the program's own constructors with named fields is a
  -- name the library writes, and its modules have the operators they had.
  -- (Each type's `Reflect` is written only where a text names reflection:
  -- otherwise nothing could ask it, and it would be read and declared for
  -- nothing. The prelude's types always have theirs.)
  let reflect := check && ((src :: own.map (·.2)) ++ library.map (·.2)).any mentionsReflection
  let kept : Option StdRead := read.bind fun r =>
    let mine := said.flatMap (·.records)
    if mine.any r.names.contains then none
    else if r.tables.all fun (p, table) => p.isEmpty || tables.lookup p == some table then some r
    else none
  -- A program's own arrays are of a length their type says, `[T; N]`:
  -- there is no growable array.
  let fixed := true
  -- (Each group of its items as an earlier compile parsed it, where it is
  -- where it was, written alike: `itemsKept`.)
  let (items, _, itemsMade) ← Trace.timed "parse: the program's text" fun _ => Syntax.parseKept fix src (base := 1000000) (records := records) (tables := tables)
    (fixed := fixed) (lexed := tokensOf []) (reflect := reflect) (kept := itemsKept)
  let declares := items.any fun
    | .module "std" _ | .pub _ (.module "std" _) => true
    | _ => false
  -- (`core` and `alloc` are the library's too: its other names for the same.)
  let items := if std && !declares then
      items ++ (["std", "core", "alloc"].filter fun r => library.any (·.1 == [r])).map fun r =>
        Syntax.Item.pub false (.module r none)
    else items
  -- (A module's items as an earlier compile parsed them from the same, where
  -- one did, `parsedKept`; and each module's items, for the next.)
  let rec fill (fuel : Nat) (path : List String) (items : List Syntax.Item) :
      StateT (List (UInt64 × List Syntax.Item)) (Except String) (List Syntax.Item) :=
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
            | some items =>
              -- (Read once without each type's `Reflect`: theirs, where the
              -- program names reflection.)
              if reflect then
                match Syntax.reflectionsOf fix items (1000000 * (k + 2) + Syntax.reflectionBase) records tables here true with
                | .ok made => pure (items ++ made)
                | .error e => throw s!"module `{shown}`: {e}"
              else pure items
            | none =>
              let text := ((files[k]?).map (·.2)).getD ""
              let base := 1000000 * (k + 2)
              -- (Every module's arrays are of a length their type says.)
              let fixed := true
              let key := parseKey text base records tables here fixed reflect
              let items ← match parsedKept[key]? with
                | some items => pure items
                | none =>
                  match Trace.timed s!"parse: module {shown}" fun _ => Syntax.parse fix text (base := base) (records := records)
                      (tables := tables) (path := here) (fixed := fixed)
                      (lexed := if k < library.length then stdTokens here text else tokensOf here) (reflect := reflect) with
                  | .ok (items, _) => pure items
                  | .error e => throw s!"module `{shown}`: {e}"
              modify ((key, items) :: ·)
              pure items
          pure (wrap (.module name (some (← fill fuel here parsed))))
        | none => throw s!"module `{shown}` has no file"
      | .module name (some body), fuel + 1 =>
        pure (wrap (.module name (some (← fill fuel (path ++ [name]) body))))
      | _, _ => pure item
  let (items, made) ← (fill 64 [] items).run []
  checkUnsafeImpls items
  pure (prelude, items, made, ownRead ++ unread, itemsMade)

/-- A program's items as the resolver gives them, each module's after a mark
(`Syntax.unitMark`), put in an order that has every module after those it
uses, the prelude's items first and the library's modules before the
program's: the items before the first mark, and each module's key and items. -/
def unitsOfBy {α : Type} (mark : α → Option String) (items : List α) (uses : List (String × List String)) :
    List α × List (String × List α) := Id.run do
  let first := items.takeWhile fun i => (mark i).isNone
  let mut units : Array (String × Array α) := #[]
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

/-- The unit a mark item begins. -/
def unitMarkOf : Syntax.Item → Option String
  | .fieldNames m [k] [] => if m == Syntax.unitMark then some k else none
  | _ => none

def unitsOfFlat (items : List Syntax.Item) (uses : List (String × List String)) :
    List Syntax.Item × List (String × List Syntax.Item) :=
  unitsOfBy unitMarkOf items uses

/-- The items without the marks of units. -/
def withoutUnitMarksFlat (items : List Syntax.Item) : List Syntax.Item :=
  items.filter fun
    | (.fieldNames m [_] []) => m != Syntax.unitMark
    | _ => true

/-- The prelude, with the standard library if `std`, checked: how many items
it is, and what the checker knows after it. A program that declares no name
the prelude has is checked from there, against what the prelude declares.
`drop`: for a program in which some type has `Drop`, checked so that a
function is given how to destroy the types it is generic in. -/
def checkFirstPart (std drop : Bool) : Except String (Nat × Check.St) := do
  if !std then
    let (prelude, _) ← readPrelude.get
    let resolved ← Syntax.Modules.resolve (Syntax.Flat.promoteItems (prelude)).1 []
    let all := withoutUnitMarksFlat (Syntax.Flat.fillDefaults (← Syntax.Flat.expandAliases resolved.items).1).1
    -- (Compacted, as a program's are before they are checked: what the
    -- check records of an expression is by its place in the body.)
    let all := all.map Syntax.Item.compact
    return (all.length, ← Check.checkFirst all resolved.info drop)
  let (prelude, items, _, _, _) ← parseProgram "// std" []
  let resolved ← Syntax.Modules.resolve (Syntax.Flat.promoteItems (prelude)).1 (Syntax.Flat.promoteItems (items)).1
  -- (Its modules in the order a program has them, marks and all, so that
  -- what a program has first is these, item for item.)
  let (first, units) := unitsOfFlat resolved.items resolved.info.unitUses
  let items := first ++ units.flatMap (fun (k, is) => (Syntax.Item.fieldNames Syntax.unitMark [k] []) :: is)
  let all := (Syntax.Flat.fillDefaults (← Syntax.Flat.expandAliases items).1).1
  -- (Without the first module's mark, at the end: it has nothing.)
  let all := match all.getLast? with
    | some ((.fieldNames m [""] [])) => if m == Syntax.unitMark then all.dropLast else all
    | _ => all
  pure (all.length, ← Check.checkFirst ((withoutUnitMarksFlat all).map Syntax.Item.compact) resolved.info drop)

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
  | .impl { trait := tr, .. } :: rest => Syntax.lastSegment tr.base == "Drop" || hasDrop rest
  | _ :: rest => hasDrop rest

/-- Elaborate, and work out the constants at compile time (`Comptime`). -/
def elaborate (items : List Syntax.Item) (blocks : Option Elab.Blocks)
    (root : String := "main") (kept : Option Elab.ElabMemo := none) :
    Except String Elab.Output := do
  Comptime.evaluate (← Elab.elabProgram items blocks root kept)

/-- (`GLORIOUS_UNLOWERED`: no program is lowered, for trying how one runs
that is not.) -/
initialize unlowered : Bool ← do pure (← IO.getEnv "GLORIOUS_UNLOWERED").isSome

/-- The program lowered by its types, where it can be: what the machines run;
taking what an earlier compile kept of each function's lowering (`kept`). -/
def Compiled.lower (kept : Option Lower.TypedMemo) (c : Compiled) : Compiled :=
  -- (The static blocks gathered first: the same for the program lowered.)
  let c := { c with core := c.core.internStatics }
  match Trace.timed "lower by types" fun _ => if unlowered then none else c.types.get.bind (Lower.program · c.core kept) with
  | some (core, copies, typedMade) =>
    { c with core, checked := c.core, lowered := true, typedMade
             fnNames := c.fnNames ++ (copies.map fun fn => (c.fnNames[fn]?).getD "").toArray }
  | none => { c with checked := c.core }

/-- Parse, check and elaborate a program together with the prelude, find its
Core's types and lower it by them. With `check := false` the check is
skipped, so that programs which go wrong can still be run, and it is not
lowered. -/
def compileSource (src : String) (check : Bool := true)
    (files : List (List String × String) := []) (few : Bool := false)
    (checkKept : Check.Kept := [])
    (firsts : List ((Bool × Bool) × (Nat × Check.St)) := [])
    (parsedKept : Parsed := {})
    (preludeKept : Option (List Syntax.Item × Syntax.Fixities) := none) (texts : Texts := {})
    (lenient : Bool := false) (groupsKept : Option Check.Deltas := none) (reachOnly : Bool := false)
    (unitsKept : Option Syntax.Modules.UnitsKept := none)
    (frontKept : Option (Std.HashMap UInt64 (List Syntax.Item)) := none)
    (itemsKept : Option Syntax.ItemsKept := none) (elabKept : Option Elab.ElabMemo := none)
    (lowerKept : Option Elab.LowerMemo := none) (typedKept : Option Lower.TypedMemo := none) :
    Except String Compiled := Compiled.lower typedKept <$> do
  -- (Each text lexed, once: each that an earlier compile read as it is,
  -- `texts`, not.)
  let lexed ← Trace.timed "lex" fun _ =>
    ((([], src) :: files).filter fun (path, text) => !texts.contains (textKey path text)).mapM fun (path, text) => do
      pure (path, ← Syntax.lex text)
  let (prelude, items, parsedMade, textsMade, itemsMade) ← Trace.timed "parse" fun _ =>
    parseProgram src files check few lexed parsedKept preludeKept texts itemsKept
  -- Every name is given its meaning: the modules become one list of items,
  -- each module a unit, after those it uses.
  -- (Resolved, and all that follows, from flat bodies.)
  -- (Each item as an earlier compile made it, where what it was made from is
  -- the same: `Syntax.Flat.FrontMemo`.)
  let front : Syntax.Flat.FrontMemo := { kept := frontKept.getD {}, keep := frontKept.isSome }
  let (flatPrelude, flatItems, front) := Trace.timed "flat bodies" fun _ =>
    let (p, front) := Syntax.Flat.promoteItems (prelude) front
    let (i, front) := Syntax.Flat.promoteItems (items) front
    (p, i, front)
  let resolved ← Trace.timed "resolve names" fun _ => Syntax.Modules.resolve flatPrelude flatItems unitsKept
  let (firstItems, unitItems) := unitsOfFlat resolved.items resolved.info.unitUses
  let resolved := { resolved with items :=
    firstItems ++ unitItems.flatMap (fun (k, is) => (Syntax.Item.fieldNames Syntax.unitMark [k] []) :: is) }
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
  let (all, front) ← Trace.timed "expand aliases" fun _ => Syntax.Flat.expandAliases resolved.items front
  -- An implementation that does not write a function its trait gives a body
  -- has that body.
  let (all, front) := Trace.timed "fill defaults, write out blankets" fun _ => Syntax.Flat.fillDefaults all front
  -- What the checker learnt about blocks that share an environment. A program
  -- it rejects is elaborated without that.
  -- (Or that has a cleanup, which a resumption given up runs: what destroys
  -- a resumption that is let go is then written.)
  let drops := hasDrop items || hasText src "defer"
  -- (The library read for this program alone is checked with it.)
  let withStd := usesStd src files && !hasText src "#![no_std]"
    && !(few && (neededStd (src :: files.map (·.2))).isSome)
    -- (Where reflection is named, the library's types have their
    -- `Reflect`, which the library checked once has not.)
    && !((src :: files.map (·.2)).any mentionsReflection)
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
  let all := Trace.timed "split fields borrowed apart" fun _ => match first with
    | .ok (count, _) => all.take count ++ Elab.splitFieldItems all (all.drop count)
    | .error _ => Elab.splitFieldItems all all
  -- (What nothing reaches of the bodies left out: what is checked, kept and
  -- hashed from here on is what is written.)
  let all := Trace.timed "compact" fun _ => all.map Syntax.Item.compact
  -- (`kept`: what an earlier check of the same program kept, in the same
  -- process: the steps whose inputs did not change are not checked again.)
  let seed := mixHash (hash withStd) (mixHash (hash drops) (hash few))
  -- (Each unit's items, in order, for the checker; and the items whole.)
  let unitList := match first with
    | .ok (count, _) => (unitsOfFlat (all.drop count) resolved.info.unitUses).2
    | .error _ => []
  let units := unitList.map (fun (u : String × List Syntax.Item) => u.2)
  -- (For each, the units before it that it uses.)
  let unitDeps := unitList.zipIdx.map fun ((k, _), i) =>
    let uses := (resolved.info.unitUses.lookup k).getD []
    ((unitList.take i).zipIdx.filter fun ((k', _), _) => uses.contains k').map (·.2)
  -- (The library's modules among them, which come first, and the program's
  -- modules that are files of their own: every unit but the program's,
  -- which come before it. Kept for any program, which starts from them
  -- where it begins with the same.)
  let library := unitList.length - 1
  let infoKeys := Trace.timed "units' keys" fun _ => unitList.zipIdx.map fun ((k, is), i) =>
    unitInfoKey resolved.info ((unitList.take i).map (·.1)) k is
  -- (And what the prelude and library checked first count, without marks.)
  let first := first.map fun (count, st) => ((withoutUnitMarksFlat (all.take count)).length, st)
  let all := withoutUnitMarksFlat all
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
      Check.checkUnitsKept { first with lenient, reachOnly } (cut (all.drop count)) resolved.info (mixHash seed (hash count)) checkKept
        (library := if (units.map List.length).sum == (all.drop count).length then library else 0)
        (deps := if (units.map List.length).sum == (all.drop count).length then unitDeps else [])
        (groupsKept := groupsKept)
    -- (A program that declares a name the prelude has: the prelude checked
    -- with it, as the first unit, and nothing taken as the program's own.)
    | true, true, .ok (count, _) =>
      Check.checkUnitsKept { dropMode := drops } ((all.take count, hash resolved.info.text) :: cut (all.drop count))
        resolved.info (mixHash seed 77) checkKept (own := false)
    | _, _, _ => ((Check.checkProgram all resolved.info drops).map (·, [], [], #[])).mapError (fun e => ({ msg := e } : Elab.Said))
  -- (What the checker finds of how the program is read once it knows
  -- types it writes where it finds it, and the elaborator alike
  -- (`Elab.decidedProgram`).)
  let checkWith := fun (all : List Syntax.Item) => (all, checkOnce all)
  let (all, checked) := Trace.timed "check" fun _ => checkWith all
  -- (Dot calls the checker chose a type's own function for, by the value's
  -- type: written so for what follows.)
  let all := Trace.timed "what the checker decided, written in" fun _ => match checked with
    | .ok (blocks, _) =>
      Elab.decidedProgram blocks all
    | .error _ => all
  let (blocks, checkMade, libraryMade, groupsMade) ← match checked with
    | .ok (blocks, made, shared, groups) => pure (some blocks, made, shared, groups)
    | .error e => if check then throw e.msg else pure (none, [], [], #[])
  -- (Where only what the checker found is asked, that is all.)
  if lenient then
    return { core := ⟨#[], .ret (.int 0), [], #[], []⟩, ctorNames := #[], fnNames := #[], opNames := #[], checkKept := checkMade }
  -- (A call of an intrinsic is the machine's operation: its declaration was
  -- the checker's alone.)
  let first := first.map fun (count, st) => ((Syntax.Item.withoutIntrinsics (all.take count)).length, st)
  let all := Syntax.Item.withoutIntrinsics all
  -- Lifetimes were the checker's to read; and, of what is declared, the
  -- typer's.
  let written := Elab.declaredOf all
  let all := Trace.timed "erase lifetimes" fun _ => Elab.eraseLifetimes all
-- From here on the program has no traits: the checker said how each bound
  -- is met, and each is now a value passed where it is needed. Lowered only
  -- as far as what is elaborated reaches (`Elab.Lower`).
  let lowering ← match blocks with
    | some b => do pure (some (← Trace.timed "lower: each function's way" fun _ => Elab.lowering b written all))
    | none => pure none
  let blocks := match lowering with
    | some L => some L.blocks
    | none => blocks
  -- What nothing reaches is not part of the program that runs. But what the
  -- program's own functions say is looked at wherever they are: one that
  -- `main` does not reach is elaborated too, for what the elaborator alone
  -- refuses, and then left out.
  -- (A coercion is reached with the function it is applied in.)
  let roots := ["main"]
  let (all, lowered) ← Trace.timed "lower what main reaches" fun _ => do
    match lowering with
    | some L =>
      let st ← L.reach { L.start with kept := lowerKept.getD {} } roots
      -- (And the coercions applied in what they reach.)
      let coerced : List String := L.blocks.coercions.fold (fun acc _ fn => if st.seen.contains fn then fn :: acc else acc) []
      pure (Elab.reachable (roots ++ coerced.eraseDups) (L.items st), some st)
    | none => pure (Elab.reachable roots all, none)
  -- (Only they and what they reach: what `main` reaches is elaborated below.
  -- Taken from the first of them, as a program is from `main`; beside what
  -- follows, on a thread of its own, and what it refuses said first.)
  -- (Where only what `main` reaches was checked, that is all that is
  -- elaborated: the rest waits for the compile after.)
  let missing := match check && !reachOnly, lowering with
    | true, some L =>
      let named := fun (items : List Syntax.Item) => items.filterMap fun
        | Syntax.Item.fn name _ _ _ _ => some name
        | _ => none
      let own := match first with
        | .ok (count, _) => named (written.drop count)
        | .error _ => []
      let reached : Std.HashSet String := all.foldl (init := {}) fun s item => match item with
        | Syntax.Item.fn name _ _ _ _ => s.insert name
        | _ => s
      -- (Those still there once traits are lowered: one made into copies is
      -- elaborated as each copy is. Not one given implementations, which is
      -- made only as copies for those it is given: checked, it is made where
      -- it is used.)
      own.filter fun f => !reached.contains f && L.fns.contains f
        && (L.blocks.traits.boundedAt[f]?).getD 0 == 0
    | _, _ => []
  let aside : Task (Except String Unit) := Task.spawn fun _ =>
    match missing.isEmpty, lowering, lowered with
    | false, some L, some st => do
      let st' ← L.reach st missing
      let coerced : List String := L.blocks.coercions.fold (fun acc _ fn => if st'.seen.contains fn then fn :: acc else acc) []
      match Trace.timed "elaborate what main does not reach" fun _ =>
          elaborate (Elab.reachable (missing ++ coerced.eraseDups) (L.items st')) blocks
            (root := missing.headD "main") with
      | .error e => .error e
      | .ok _ => .ok ()
    | _, _, _ => .ok ()
  let declared := Trace.timed "what is declared" fun _ => Elab.withDeclared written (Elab.declaredOf all)
  -- (What a compile gives, from what was elaborated, with Core's types.)
  let compiled := fun (out : Elab.Output) (types : Option Lower.Types) =>
    ({ core := out.program, ctorNames := out.ctorNames.map shownName, fnNames := out.fnNames
       opNames := out.opNames, types := Thunk.pure types, checkKept := checkMade
       firstMade, libraryKept := libraryMade, groupsMade, unitsMade := resolved.unitsMade, frontMade := front.made,
       parsedMade, textsMade, itemsMade, elabMade := out.made
       lowerMade := match lowered with
         | some st => st.keptMade
         | none => {} } : Compiled)
  let build := fun (blocks : Option Elab.Blocks) => do
    let out ← match Trace.timed "elaborate" fun _ => elaborate all blocks (kept := elabKept) with
      | .ok out => do aside.get; pure out
      | .error e => do aside.get; throw e
    -- Core's types, for the lowering (`Typer`). Where they are not found,
    -- the program runs as it is.
    let types : Except String (Option Lower.Types) := if !check then .ok none else
      match Trace.timed "types" fun _ => Typer.typesOf declared out with
      | .ok types =>
        if Trace.typesTraced then dbgTrace (Core.showCore out.fnNames out.program ++ "\n" ++ Typer.showSigs types) fun _ => .ok (some types)
        else .ok (some types)
      | .error e =>
        -- (`GLORIOUS_TRACE`: why there are none.)
        if Trace.enabled then dbgTrace s!"no types: {withFnNames out.fnNames e}" fun _ => .ok none
        else .ok none
    pure (compiled out (← types))
  build blocks

/-- The characters of a text, if the value is one: a text written out in a
program that is not checked (`Syntax.textItem`), or a line written; whose
constructors are shown under names no program can write. -/
partial def textOf (names : Array String) : Value → Option (List Nat)
  -- (A line written by `host_line`.)
  | .data tag fields =>
    if tag == textLineTag then fields.mapM (fun | .int c => some c.toNat | _ => none) else
    match fields with
    | [] => if names[tag]? == some Syntax.textEndName then some [] else none
    | [.int c, rest] => if names[tag]? == some Syntax.textCharName then (textOf names rest).map (c.toNat :: ·) else none
    | _ => none
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
      else if fixedBase ≤ tag then s!"[{args}]"
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
def evalCompiled (c : Compiled) (input : List Int := []) (fuel : Nat := 200000) (vmScale : Nat := 20) : String :=
  let bytecode := compile c.core
  let onCore := showOutcome c.ctorNames
    (Machine.exec (Core.stepIO c.core) fuel (Core.initIO c.core input))
  let onVm := showOutcome c.ctorNames
    (Machine.exec (Bytecode.stepIO bytecode) (fuel * vmScale) (Bytecode.initIO bytecode input))
  -- (A program the Core machine does not finish in its steps, and bytecode
  -- does in `vmScale` times as many: as long programs are, run on bytecode
  -- alone.)
  if onCore == onVm || (onCore == "out of fuel" && onVm != "out of fuel") then onVm
  else s!"MISMATCH: Core gives {onCore}, bytecode gives {onVm}"

/--
Compile a program and run it on both machines with the given input. The result
is what it wrote followed by its value, or a description of what went wrong; if
the machines disagree, both are shown.
-/
def evalSource (src : String) (input : List Int := []) (fuel : Nat := 200000) : String :=
  match compileSource src with
  | .error e => s!"error: {e}"
  | .ok c => evalCompiled c input fuel

/-- Is `sub` this term or one it goes on to? -/
partial def tmHas (t sub : Core.Tm) : Bool :=
  t == sub || match t with
    | .let_ _ b | .call _ _ b | .handle _ _ _ _ b | .perform _ _ b | .label _ b | .guard _ _ b
    | .cancel _ b | .cell _ _ b | .cellL _ _ _ b | .lend _ _ _ _ _ b | .mem _ _ b | .host _ _ b => tmHas b sub
    | _ => false

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
            if fixedBase ≤ tag then s!"place `{i}` is asked of an array of {fields.length}"
            else s!"an arithmetic intrinsic is applied to ({shown vs})"
          | _ => s!"an arithmetic intrinsic is applied to ({shown vs})"
      | none => unbound
    | .place pl =>
      -- (In the function whose code it is, where one is found.)
      -- (Said only where one function has the code: the same code may be
      -- in several.)
      let within := match c.core.fns.toList.zipIdx.filter fun (f, _) => f.clauses.any (tmHas ·.body s.tm) with
        | [(_, k)] => some s!" (in {fnName k})"
        | _ => none
      match s.env[pl.var]? with
      | some v => s!"`{showValue c.ctorNames v}` does not have the field being read{within.getD ""}"
      | none => unbound
    | _ => unbound
  | .call f args _ | .tail f args => applied f (evalAtoms s.env args)
  | .handle _ _ _ thunk _ | .handleTail _ _ _ thunk => applied thunk (some [])
  | .label thunk _ | .labelTail thunk => applied thunk (some [.label s.store.labels])
  | .guard _ thunk _ | .guardTail _ thunk => applied thunk (some [])
  | .raise op _ | .perform op _ _ => performed op
  | .cancel _ _ => "`cancel` is applied to something that is not a usable resumption"
  | .cell _ thunk _ | .cellTail _ thunk => applied thunk (some [.ref s.store.cells.size 0 []])
  | .cellL l init _ _ | .cellTailL l init _ =>
    let v := (init.eval s.env).map (showValue c.ctorNames) |>.getD "?"
    s!"a cell of memory could not be made: `{v}` is not laid out as {l.lay.show}"
  | .lend _ r thunk pre post _ =>
    match r.eval s.env with
    | some (.ref a _ path) =>
      applied thunk (do
        pure ((← evalAtoms s.env pre) ++ .ref a (s.store.labels + 1) path
          :: (← evalAtoms s.env post)))
    | some v => s!"`{showValue c.ctorNames v}` is lent, but it is not a reference"
    | none => unbound
  | .mem op args _ =>
    match evalAtoms s.env args with
    | some (.ref _ _ _ :: _) => "a reference is used after the cell it points to was freed"
    | some vs => s!"a memory operation ({op.name}) is applied to ({shown vs}), which is not a reference"
    | none => unbound
  | .host id _ _ =>
    if id ≥ 6 then "a shared cell is used that is not there, or holds nothing"
    else if id ≥ 2 then "a foreign function or memory at an address has no meaning on this machine: build the program and run it on the Rust VM"
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

/-- A program run on the bytecode machine to its end: `seen` of each state
before its step, carried along, and `last` of it and the state the last step
leaves. None where it does not compile, is stuck or runs out of `fuel`. -/
def runBytecode {α β : Type} (src : String) (input : List Int) (fuel : Nat) (init : α)
    (seen : α → Bytecode.Config → α) (last : α → Bytecode.Config → β) : Option β :=
  match compileSource src with
  | .error _ => none
  | .ok c =>
    let bytecode := compile c.core
    let rec go : Nat → Bytecode.Config → α → Option β
      | 0, _, _ => none
      | n + 1, cfg, acc =>
        let acc := seen acc cfg
        match Bytecode.stepIO bytecode cfg with
        | .next cfg' => go n cfg' acc
        | .halt _ => some (last acc cfg)
        | .stuck => none
    go fuel (Bytecode.initIO bytecode input) init

/-- The deepest the bytecode machine's stack gets while running a program. -/
def peakStack (src : String) (input : List Int := []) (fuel : Nat := 4000000) : Option Nat :=
  runBytecode src input fuel 0 (fun peak cfg => max peak cfg.state.frames.length) fun peak _ => peak

/-- How many memory cells are still live when a program finishes, cells and
blocks of memory alike. The step that ends the program also leaves the scopes
still on the stack, so their cells do not count. -/
def liveCells (src : String) (input : List Int := []) (fuel : Nat := 4000000) : Option Nat :=
  runBytecode src input fuel () (fun _ _ => ()) fun _ cfg =>
    let leaving := cfg.state.frames.filterMap fun
      | .cell a => some a
      | _ => none
    let cells := cfg.state.store.cells
    ((List.range cells.size).filter fun a => (cells[a]?.getD none).isSome && !leaving.contains a).length
      + (cfg.state.store.mem.blocks.keys.filter (!leaving.contains ·)).length

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
