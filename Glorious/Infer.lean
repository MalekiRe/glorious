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
  | .perform _ _ body | .label _ body => tmRefs body
  | .labelTail _ => []
  | .cell _ _ body | .cellL _ _ _ body | .lend _ _ _ _ _ body => tmRefs body
  | .cellTail _ _ | .cellTailL _ _ _ => []
  | .guard _ _ body => tmRefs body
  | .guardTail _ _ => []
  | .cancel _ body | .mem _ _ body | .host _ _ body => tmRefs body

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
    | .cell _ _ body | .cellL _ _ _ body => visit out body
    | .lend _ _ _ _ _ body => visit out body
    | .cellTail _ _ | .cellTailL _ _ _ => out
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
  -- (Looked up by function: each list once into a map.)
  let givenUpBy : Std.HashMap Nat Nat := st.givenUp.foldl (fun m (f, a) => m.insertIfNew f a) {}
  let dropsBy : Std.HashMap Nat Nat := p.drops.foldl (fun m (f, d) => m.insertIfNew f d) {}
  let anySet : Std.HashSet Nat := st.anyCallable.foldl (·.insert ·) {}
  -- (Each function by its name, and which of those of the name it is; a
  -- closure, which has none, by the function that first makes it and which
  -- of what that one names it is: an edit that moves the others, `main`'s
  -- reaching more first, keys none of them anew.)
  let named0 : Array UInt64 := (p.names.foldl (fun (acc : Array UInt64 × Std.HashMap String Nat) nm =>
      let k := acc.2.getD nm 0
      (acc.1.push (hash (nm, k)), acc.2.insert nm (k + 1))) (#[], {})).1
  let sids : Array UInt64 := Id.run do
    let top := named0.size
    let mut sids : Array UInt64 := named0 ++ ((List.range (st.fns.size - top)).map fun k => hash (top + k)).toArray
    let mut known : Std.HashSet Nat := {}
    let mut queue : Array Nat := (List.range top).toArray
    let mut i := 0
    while i < queue.size do
      let f := queue[i]!
      i := i + 1
      -- (And what destroys a closure of it, after what it names.)
      let refs := (((st.fns[f]?).map fun F => F.clauses.flatMap fun c => tmRefs c.body).getD [])
        ++ (dropsBy[f]?).toList
      for (g, j) in refs.zipIdx do
        if top ≤ g && !known.contains g then
          known := known.insert g
          sids := sids.set! g (mixHash sids[f]! (hash j))
          queue := queue.push g
    pure sids
  let sid := fun (f : Nat) => (sids[f]?).getD (hash f)
  -- (And each block of bytes by its bytes, not where it is among them.)
  let statics := p.statics.toArray
  let named := fun (t : Core.Tm) =>
    (t.mapFns fun g => (sid g).toNat).mapStatics fun i => (hash (statics[i.toNat]?)).toNat
  let extra := fun (f : Nat) =>
    hash (st.armFns.contains f, st.ncaps[f]?, givenUpBy[f]?, anySet.contains f,
      (dropsBy[f]?).map sid, (capBy.getD f []).mergeSort (fun (a : Nat × Nat) b => a.1 ≤ b.1))
  -- (What closures capture and which destroy which are each function's,
  -- in `extra`: a change to one function's is not every function's.)
  let globals := hash (items.filter (fun
      | .fn .. => false
      | .pub _ (.fn ..) => false
      | _ => true),
    st.strict, st.regions, st.loans, st.ranked, st.widen, st.anyUnknown)
  let n := st.fns.size
  let members := (List.range n).foldl (fun (m : Std.HashMap Nat (List Nat)) f =>
    let r := (st.scc[f]?).getD f
    m.insert r ((m.getD r []) ++ [f])) {}
  let outside := members.fold (fun (o : Std.HashMap Nat (List Nat)) r ms =>
    o.insert r ((ms.flatMap fun f => ((st.fns[f]?).map fun F => F.clauses.flatMap fun c => tmRefs c.body).getD []).filterMap
      (fun g => let rg := (st.scc[g]?).getD g; if rg == r then none else some rg) |>.eraseDups)) {}
  modify fun s =>
    { s with
      keyed := !(st.memo.isEmpty && st.frozen.isEmpty && st.keptMains.isEmpty && !st.remember)
      ownKeys := (List.range n).toArray.map fun f =>
        mixHash (hash (st.fns[f]?.map (·.clauses.map fun c => { c with body := named c.body }))) (extra f)
      sids, bySid := sids.zipIdx.foldl (fun m (k, f) => m.insert k f) {}
      members, outside, keyBase := globals }
  let τ ← freshTy
  -- (`main`'s key, for what an earlier compile kept: what it is made of,
  -- and what each group it uses shows it, as a group's key is.)
  let mainKey ← (fun s => Trace.timed "infer: main's key" fun _ => (do
    if !(← get).keyed then pure (0 : UInt64) else do
    let mut k := mixHash st.keyBase (hash (named p.main))
    for g in ((tmRefs p.main).map fun f => (st.scc[f]?).getD f).eraseDups do
      k := mixHash k (← faceOf g)
    pure k : M UInt64).run s : M UInt64)
  -- (Kept, where every function it uses has the key it had: what it was
  -- found to be is taken, the regions of each use made anew.)
  let keptMain ← match (← get).keptMains[mainKey]? with
    | some m =>
      if mainKey == 0 then pure none else do
      let byKey := (← get).byKey
      let wanted := m.wanted.filterMap fun (k, sig, atoms, own, more) => (byKey.get? k).map (·, sig, atoms, own, more)
      if wanted.length != m.wanted.length then pure none else do
      let mut fresh : Std.HashMap Nat Nat := {}
      let mut uses : List (Nat × Use) := []
      for (g, sig, atoms, own, more) in wanted do
        for a in atoms ++ own.toList ++ more do
          unless fresh.contains a do fresh := fresh.insert a (← freshAtom)
        let at_ := fun (a : Nat) => fresh.getD a a
        uses := uses ++ [(g, ⟨sig, atoms.map at_, own.map at_, more.map at_⟩)]
      -- (And kept again, for the compile after.)
      modify fun s => { s with mainsMade := s.mainsMade.push (mainKey, m) }
      pure (some (m.ty, m.hints, uses))
    | none => pure none
  let (mainTy, mainHints, wanted) ← match keptMain with
    | some found => pure found
    | none => do
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
      -- (Kept for the next compile, by the keys of the functions it uses.)
      if mainKey != 0 && (← get).remember then
        let keys ← wanted.mapM fun (g, u) => do pure (← fnKey g, u.sig, u.atoms, u.own, u.more)
        unless keys.any (·.1 == 0) do
          modify fun s => { s with mainsMade := s.mainsMade.push (mainKey, ⟨mainTy, mainHints, keys⟩) }
      pure (mainTy, mainHints, wanted)
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
    (memo : Memo := {}) (remember : Bool := true) (anyUnknown : Bool := false) :
    Except String (Cert × Made) := do
  let g ← Elab.collectDeclared items
  match (certifyM items g p envSizes).run
    { fns := p.fns, strict, regions, loans, ranked, widen, anyUnknown, memo := memo.inst
      frozen := memo.schemes, keptFaces := memo.faces, keptMains := memo.mains, remember } with
  | .ok cert st => pure (cert, ⟨st.made, st.frozenMade, st.facesMade, st.mainsMade⟩)
  | .error e _ => throw e

/-- The certificate alone, with nothing kept. -/
def certify (items : List Item) (p : Core.Program) (strict : Bool)
    (envSizes : List (Nat × Nat × Nat) := []) (regions loans ranked widen : Bool := false)
    (anyUnknown : Bool := false) : Except String Cert :=
  (·.1) <$> certifyKept items p strict envSizes regions loans ranked widen (remember := false) (anyUnknown := anyUnknown)

/-- What was made, as kept for the next compile. -/
def toMemo (made : Made) : Memo :=
  { inst := made.inst.foldl (fun m (k, sig, r) =>
      let old := m.getD k []
      if old.any (·.1 == sig) then m else m.insert k ((sig, r) :: old)) {}
    schemes := made.schemes.foldl (fun m (k, fz) => m.insert k fz) {}
    faces := made.faces.foldl (fun m (k, f) => m.insert k f) {}
    mains := made.mains.foldl (fun m (k, f) => m.insert k f) {} }

/-- Which part of a program a certificate fails on, for reporting a defect in
this pass or in the elaborator. -/
def rejected (C : Cert) (p : Core.Program) : String :=
  let bad := C.sigs.toList.filterMap fun e =>
    match p.fns[e.fn]? with
    | some F =>
      if Typing.checkFn C e F then none
      else if !Typing.checkClauses C e.sig F.clauses e.hints then
        some s!"function {e.fn} is not typed at one of its signatures: {showSig e.sig}"
      else some s!"the clauses of function {e.fn} are not shown to cover its parameters"
    | none => some s!"function {e.fn} does not exist"
  match bad with
  | msg :: _ => msg
  | [] =>
    if Typing.checkTm C [] [] p.main C.mainHints C.mainTy [] then "nothing" else "`main` is not typed"

end Glorious.Infer
