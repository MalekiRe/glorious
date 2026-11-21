module

public import Glorious.Infer.Read
public import Glorious.Trace

public section

namespace Glorious.Infer

open Syntax
open Glorious.Typing (Ty FnSig Hint Cert SigEntry DataInst OpInst)

/-! ## Recursive groups -/

partial def tmRefs : Core.Tm → List Nat
  | .ret _ => []
  | .let_ rhs body =>
    (match rhs with
      | .closure fn _ => [fn]
      | .rebind _ fn => [fn]
      | _ => []) ++ tmRefs body
  | .call _ _ body => tmRefs body
  | .tail _ _ => []
  | .handle ret ops _ _ body => ret :: ops.map (·.2) ++ tmRefs body
  | .handleTail ret ops _ _ => ret :: ops.map (·.2)
  | .raise _ _ => []
  | .perform _ _ body => tmRefs body
  | .label _ body => tmRefs body
  | .labelTail _ => []
  | .cell _ _ body => tmRefs body
  | .lend _ _ _ _ _ body => tmRefs body
  | .cellTail _ _ => []
  | .guard _ _ body => tmRefs body
  | .guardTail _ _ => []
  | .cancel _ body => tmRefs body
  | .mem _ _ body => tmRefs body
  | .host _ _ body => tmRefs body

/-- For each function, the least function it is mutually recursive with:
the strongly connected parts of what each refers to (Tarjan's way, with a
stack of its own in place of recursion). -/
def sccs (fns : Array Core.Fn) : Array Nat := Id.run do
  let n := fns.size
  let refs : Array (Array Nat) := fns.map fun F =>
    ((F.clauses.flatMap fun c => tmRefs c.body).filter (· < n)).toArray
  let unseen := n + 1
  let mut index : Array Nat := Array.replicate n unseen
  let mut low : Array Nat := Array.replicate n 0
  let mut onStack : Array Bool := Array.replicate n false
  let mut stack : Array Nat := #[]
  let mut out : Array Nat := Array.replicate n 0
  let mut counter := 0
  for root in [0:n] do
    if index[root]! != unseen then continue
    -- (Each frame: a function and how many of its references are done.)
    let mut frames : Array (Nat × Nat) := #[(root, 0)]
    index := index.set! root counter
    low := low.set! root counter
    counter := counter + 1
    stack := stack.push root
    onStack := onStack.set! root true
    while !frames.isEmpty do
      let (v, k) := frames.back!
      let rs := refs[v]!
      if k < rs.size then
        frames := frames.set! (frames.size - 1) (v, k + 1)
        let w := rs[k]!
        if index[w]! == unseen then
          index := index.set! w counter
          low := low.set! w counter
          counter := counter + 1
          stack := stack.push w
          onStack := onStack.set! w true
          frames := frames.push (w, 0)
        else if onStack[w]! then
          low := low.set! v (min low[v]! index[w]!)
      else
        frames := frames.pop
        if let some (u, _) := frames.back? then
          low := low.set! u (min low[u]! low[v]!)
        if low[v]! == index[v]! then
          -- (The part `v` roots: each its least member.)
          let mut members : Array Nat := #[]
          let mut going := true
          while going do
            match stack.back? with
            | some w =>
              stack := stack.pop
              onStack := onStack.set! w false
              members := members.push w
              if w == v then going := false
            | .none => going := false
          let least := members.foldl min v
          for w in members do out := out.set! w least
  pure out

/-- Say which uses of declared types are duplicable: all of them, except those
with a field that is not, found by taking flags away until nothing changes. -/
partial def dupFlags (datas : List DataInst) : List DataInst :=
  let C : Cert := ⟨#[], datas, [], .int, [], true, false, false, #[]⟩
  let next := datas.map fun d =>
    { d with dup := d.dup && d.ctors.all fun c => Typing.dupTys C c.2 }
  if next.zip datas |>.all (fun (a, b) => a.dup == b.dup) then next else dupFlags next

/-! ## The certificate -/

/-- The functions that are the arms of some handler of the program. -/
def armsOf (p : Core.Program) : Std.HashSet Nat := Id.run do
  let rec visit (acc : Std.HashSet Nat) : Core.Tm → Std.HashSet Nat
    | .handle _ ops _ _ body => visit (ops.foldl (fun a o => a.insert o.2) acc) body
    | .handleTail _ ops _ _ => ops.foldl (fun a o => a.insert o.2) acc
    | .let_ _ body | .call _ _ body | .perform _ _ body | .label _ body | .cell _ _ body
    | .lend _ _ _ _ _ body | .guard _ _ body | .cancel _ body | .mem _ _ body | .host _ _ body =>
      visit acc body
    | _ => acc
  let mut acc : Std.HashSet Nat := {}
  for F in p.fns do
    for c in F.clauses do
      acc := visit acc c.body
  visit acc p.main

/-- What is known of a local, for how many arguments a callable it holds
takes: nothing, that number, or that it is what a function captured there. -/
inductive Slot where
  | none
  | arity (n : Nat)
  | cap (fn j : Nat)

def patBinds : Core.Pat → Nat
  | .bind => 1
  | .ctor _ ps => ps.attach.foldl (fun n ⟨q, _⟩ => n + patBinds q) 0
  | _ => 0

/-- For each function and place among its captures, how many arguments the
callable it captured there takes, where every closure made of it says the
same: what is given up without its type known in the function's own body
is then known to be such a callable. -/
partial def captureArities (p : Core.Program) (ncaps : Array Nat) : Std.HashMap (Nat × Nat) Nat :=
  Id.run do
  let fnsArr := p.fns
  let arityOf := fun (g : Nat) =>
    match fnsArr[g]? with
    | some ⟨c :: _⟩ => Slot.arity c.pats.length
    | _ => Slot.none
  let rec visit (env : Array Slot) (acc : Array ((Nat × Nat) × Slot)) : Core.Tm → Array ((Nat × Nat) × Slot)
    | .let_ rhs body =>
      match rhs with
      | .closure g caps => visit (env.push (arityOf g)) (record env acc g caps) body
      | .rebind _ g => visit (env.push (arityOf g)) acc body
      | .atom (.var i) => visit (env.push (env[i]?.getD .none)) acc body
      | _ => visit (env.push .none) acc body
    | .handle ret ops caps _ body =>
      visit (env.push .none) ((ret :: ops.map (·.2)).foldl (fun a g => record env a g caps) acc) body
    | .handleTail ret ops caps _ => (ret :: ops.map (·.2)).foldl (fun a g => record env a g caps) acc
    | .call _ _ body | .perform _ _ body | .label _ body | .cell _ _ body
    | .lend _ _ _ _ _ body | .guard _ _ body | .cancel _ body | .mem _ _ body | .host _ _ body =>
      visit (env.push .none) acc body
    | _ => acc
  let mut found : Array ((Nat × Nat) × Slot) := #[]
  for (F, f) in p.fns.zipIdx do
    for c in F.clauses do
      let env := (Array.replicate c.pats.length Slot.none)
        ++ ((List.range (ncaps[f]?.getD 0)).map fun j => Slot.cap f j).toArray
        ++ Array.replicate (c.pats.foldl (fun n q => n + patBinds q) 0) Slot.none
      found := visit env found c.body
  -- (Where captures are captured again, what the first says.)
  let mut known : Std.HashMap (Nat × Nat) Nat := {}
  let mut bad : Std.HashSet (Nat × Nat) := {}
  for _ in [0:8] do
    for (key, s) in found do
      let n := match s with
        | .arity n => some n
        | .cap f j => known[(f, j)]?
        | .none => none
      match n, known[key]? with
      | some n, none => if !bad.contains key then known := known.insert key n
      | some n, some m => if n != m then bad := bad.insert key
      | none, _ => pure ()
  for (key, s) in found do
    if let .none := s then bad := bad.insert key
  pure (bad.fold (fun k b => k.erase b) known)
where
  record (env : Array Slot) (acc : Array ((Nat × Nat) × Slot)) (g : Nat) (caps : List Atom) :=
    caps.zipIdx.foldl (fun acc (a, j) =>
      match a with
      | .var i => acc.push ((g, j), env[i]?.getD .none)
      | _ => acc) acc

/-- How many values each function captures, read off the places that build it. -/
def captureCounts (p : Core.Program) : Array Nat := Id.run do
  let mut out := Array.replicate p.fns.size 0
  let rec visit (out : Array Nat) : Core.Tm → Array Nat
    | .ret _ => out
    | .let_ rhs body =>
      match rhs with
      | .closure fn captures => visit (out.setIfInBounds fn captures.length) body
      | _ => visit out body
    | .call _ _ body => visit out body
    | .tail _ _ => out
    | .handle ret ops captures _ body =>
      visit ((ret :: ops.map (·.2)).foldl (fun o f => o.setIfInBounds f captures.length) out) body
    | .handleTail ret ops captures _ =>
      (ret :: ops.map (·.2)).foldl (fun o f => o.setIfInBounds f captures.length) out
    | .raise _ _ => out
    | .perform _ _ body => visit out body
    | .label _ body => visit out body
    | .labelTail _ => out
    | .cell _ _ body => visit out body
    | .lend _ _ _ _ _ body => visit out body
    | .cellTail _ _ => out
    | .guard _ _ body => visit out body
    | .guardTail _ _ => out
    | .cancel _ body => visit out body
    | .mem _ _ body => visit out body
    | .host _ _ body => visit out body
  for F in p.fns do
    for c in F.clauses do
      out := visit out c.body
  visit out p.main

def certifyM (items : List Item) (g : Elab.Globals) (p : Core.Program)
    (envSizes : List (Nat × Nat × Nat)) : M Cert := do
  (fun s => Trace.timed "infer: declare" fun _ => (declare items g).run s : M Unit)
  modify fun s =>
    { s with
      anyCallable :=
        (g.fns[implFnName Syntax.destroyTrait Syntax.callableHead Syntax.destroyFn]?).toList
          ++ p.drops.map (·.2)
      armFns := armsOf p
      capArities := captureArities p
        (envSizes.foldl (fun acc (fn, n, _) => acc.setIfInBounds fn n) (captureCounts p))
      scc := sccs s.fns
      ncaps := envSizes.foldl (fun acc (fn, n, _) => acc.setIfInBounds fn n) (captureCounts p)
      givenUp := envSizes.map fun (fn, _, arity) => (fn, arity)
      globalTys := s.tys.size, globalRows := s.rows.size, globalClss := s.clss.size
      globalAccs := s.accs.size }
  -- (Each function's key, for what an earlier compile kept.)
  let st ← get
  let capBy := st.capArities.fold (fun (m : Std.HashMap Nat (List (Nat × Nat))) (g, at_) k =>
    m.insert g ((at_, k) :: m.getD g [])) {}
  let extra := fun (f : Nat) =>
    hash (st.armFns.contains f, st.ncaps[f]?, st.givenUp.lookup f, st.anyCallable.contains f,
      p.drops.lookup f, (capBy.getD f []).mergeSort (fun (a : Nat × Nat) b => a.1 ≤ b.1))
  let globals := hash (items.filter (fun
      | .fn .. => false
      | .pub _ (.fn ..) => false
      | _ => true),
    envSizes, st.strict, st.regions, st.loans, st.ranked, st.widen, p.drops)
  let n := st.fns.size
  let members := (List.range n).foldl (fun (m : Std.HashMap Nat (List Nat)) f =>
    let r := (st.scc[f]?).getD f
    m.insert r ((m.getD r []) ++ [f])) {}
  let outside := members.fold (fun (o : Std.HashMap Nat (List Nat)) r ms =>
    o.insert r ((ms.flatMap fun f => ((st.fns[f]?).map fun F => F.clauses.flatMap fun c => tmRefs c.body).getD []).filterMap
      (fun g => let rg := (st.scc[g]?).getD g; if rg == r then none else some rg) |>.eraseDups)) {}
  modify fun s =>
    { s with
      keyed := !(st.memo.isEmpty && st.frozen.isEmpty && !st.remember)
      ownKeys := (List.range n).toArray.map fun f => mixHash (hash (st.fns[f]?.map (·.clauses))) (extra f)
      members, outside, keyBase := globals }
  let τ ← freshTy
  (fun s => Trace.timed "infer: main" fun _ => (do inferTm (← freshAcc) ⟨[], none⟩ τ #[] p.main : M Unit).run s : M Unit)
  let mainHints := (← get).hints
  let refs := (← get).refs
  (fun s => Trace.timed "infer: settle" fun _ => (settleAll).run s : M Unit)
  -- A callable type a declaration writes says nothing of regions, so a callable
  -- kept in such a place can touch none.
  -- (But for the regions its own type binds.)
  for g in [0:(← get).globalAccs] do
    let own ← bindersOf g
    unless ((← accSet g).filter fun r => !own.contains r).isEmpty do
      throw "region: a callable kept in a declared type touches a mutable variable"
  let mainTy ← zonk {} τ
  let mainHints ← zonkHints {} mainHints
  let wanted ← refs.toList.mapM fun (g, gs) => do pure (g, (← demand {} gs).1)
  modify fun s =>
    { s with incls := #[], places := #[], coerces := #[], nevers := #[], onces := #[], shows := #[] }
  (fun s => Trace.timed "infer: instantiate" fun _ => (do for (g, gs) in wanted do instantiate g gs : M Unit).run s : M Unit)
  -- A function whose closures say how they are destroyed: the function that
  -- destroys one, at each of its signatures (`Typing.dropSig`). It is
  -- inferred at the regions the captures mention, and then said at all the
  -- closure's: those it does not mention it has no use for.
  let mut done : List (Nat × FnSig) := []
  let mut again := true
  while again do
    again := false
    for e in (← get).entries.toList do
      if let some d := p.drops.lookup e.fn then
        unless done.contains (e.fn, e.sig) do
          done := (e.fn, e.sig) :: done
          again := true
          let full := Typing.dropSig e.sig
          let k := ((List.range (e.sig.crgns + 1)).find? fun c => e.sig.caps.all (Ty.within c)).getD
            e.sig.crgns
          let want := { full with crgns := k }
          -- (Its regions are the closure's, fixed when it was made: one each.)
          let atoms ← (List.range k).mapM fun _ => freshAtom
          instantiate d ⟨want, atoms, none, []⟩
          let s ← get
          unless (s.emitted[d]?.getD []).contains full do
            if let some e' := s.entries.find? (fun x => x.fn == d && x.sig == want) then
              modify fun s =>
                { s with
                  emitted := let old := s.emitted.getD d []; s.emitted.insert d (full :: old)
                  entries := s.entries.push ⟨d, full, e'.hints⟩ }
  let entries := (← get).entries.toList
  let types : List Ty :=
    mainTy :: mainHints.flatMap hintTypes
      ++ entries.flatMap fun e =>
        e.sig.caps ++ e.sig.params ++ [e.sig.ret] ++ e.sig.eff.flatMap (·.2)
          ++ e.hints.flatMap (·.flatMap hintTypes)
  let opsUsed : List (Nat × List Ty) :=
    mainHints.flatMap hintOps
      ++ entries.flatMap fun e => e.sig.eff ++ e.hints.flatMap (·.flatMap hintOps)
  -- (Each type once, where it is first: one met again says nothing new.)
  let types := (types.foldl (fun (acc : Array Ty × Std.HashSet Ty) t =>
    if acc.2.contains t then acc else (acc.1.push t, acc.2.insert t)) (#[], {})).1.toList
  let (datas, ops) ← (fun s => Trace.timed "infer: decls" fun _ => (declsFor types opsUsed).run s : M _)
  let strict := (← get).strict
  pure (Cert.withIndex ⟨entries.toArray, dupFlags datas, ops, mainTy, mainHints, strict, (← get).regions,
    (← get).regions && (← get).loans, #[]⟩)

/-- Find a certificate for an elaborated program, with the ownership rules or
without, and with the region rules or without; taking what an earlier compile
kept of its inference (`memo`) and, if `remember`, giving what this one made,
to be kept for the next. -/
def certifyKept (items : List Item) (p : Core.Program) (strict : Bool)
    (envSizes : List (Nat × Nat × Nat) := []) (regions loans ranked widen : Bool := false)
    (memo : Memo := {}) (remember : Bool := true) : Except String (Cert × Made) := do
  let g ← Elab.collectDeclared items
  let (cert, st) ← (certifyM items g p envSizes).run
    { fns := p.fns, strict, regions, loans, ranked, widen, memo := memo.inst
      frozen := memo.schemes, keptFaces := memo.faces, remember }
  pure (cert, ⟨st.made, st.frozenMade, st.facesMade⟩)

/-- The certificate alone, with nothing kept. -/
def certify (items : List Item) (p : Core.Program) (strict : Bool)
    (envSizes : List (Nat × Nat × Nat) := []) (regions loans ranked widen : Bool := false) :
    Except String Cert :=
  (·.1) <$> certifyKept items p strict envSizes regions loans ranked widen (remember := false)

/-- What was made, as kept for the next compile. -/
def toMemo (made : Made) : Memo :=
  { inst := made.inst.foldl (fun m (k, sig, r) =>
      let old := m.getD k []
      if old.any (·.1 == sig) then m else m.insert k ((sig, r) :: old)) {}
    schemes := made.schemes.foldl (fun m (k, fz) => m.insert k fz) {}
    faces := made.faces.foldl (fun m (k, f) => m.insert k f) {} }

/-- Which part of a program a certificate fails on, for reporting a defect in
this pass or in the elaborator. -/
def rejected (C : Cert) (p : Core.Program) : String :=
  let bad := C.sigs.toList.filterMap fun e =>
    match p.fns[e.fn]? with
    | some F =>
      if Typing.checkFn C e F then none
      else if !Typing.checkClauses C e.sig F.clauses e.hints then
        some s!"function {e.fn} is not typed at one of its signatures"
      else some s!"the clauses of function {e.fn} are not shown to cover its parameters"
    | none => some s!"function {e.fn} does not exist"
  match bad with
  | msg :: _ => msg
  | [] =>
    if Typing.checkTm C [] [] p.main C.mainHints C.mainTy [] then "nothing" else "`main` is not typed"

end Glorious.Infer
