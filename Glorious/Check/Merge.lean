module

public import Glorious.Check.Expr

public section

namespace Glorious.Check

open Syntax

/-! ## Two checks that went on from one state, put together

Units that do not use each other are checked side by side, each from the
state after the units before them, its ids numbered from a place of its own
(`Store.jumpTo`). What each added is put together here, as if one had been
checked after the other. What both changed of what was there before, or
anything not made by adding, is not put together (none): the units are then
checked one after another. -/

unsafe def samePtrImpl {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/-- Are these the same object? (Taken to be not, where that cannot be asked.) -/
@[implemented_by samePtrImpl] def samePtr {α : Type} (_ _ : α) : Bool := false

/-- Two lists grown from `p`, by adding in front or at the end. -/
def mergeList {α : Type} (p a b : List α) : Option (List α) :=
  if samePtr a p then some b else if samePtr b p then some a else
  let lp := p.length
  let la := a.length
  let lb := b.length
  if la < lp || lb < lp then none
  else if samePtr (a.drop (la - lp)) p && samePtr (b.drop (lb - lp)) p then some (b.take (lb - lp) ++ a)
  else if ((a.take lp).zip p).all (fun (x, y) => samePtr x y) && ((b.take lp).zip p).all (fun (x, y) => samePtr x y) then
    some (a ++ b.drop lp)
  else none

/-- Two arrays grown from `p` at the end. -/
def mergeArr {α : Type} (p a b : Array α) : Option (Array α) :=
  if samePtr a p then some b else if samePtr b p then some a else
  let lp := p.size
  if a.size < lp || b.size < lp then none
  else if (List.range lp).all (fun i => match a[i]?, b[i]?, p[i]? with
      | some x, some y, some z => samePtr x z && samePtr y z
      | _, _, _ => false) then
    some (a ++ b.extract lp b.size)
  else none

/-- Two segments grown from `p`: each piece changed by at most one of them. -/
def mergeSeg {α : Type} (p a b : Seg α) : Option (Seg α) := do
  if samePtr a p then return b
  if samePtr b p then return a
  let mut out : Array (Array α) := #[]
  for i in [0:max a.pieces.size b.pieces.size] do
    let pa := a.pieces.getD i #[]
    let pb := b.pieces.getD i #[]
    let pp := p.pieces.getD i #[]
    if samePtr pb pp || pb.isEmpty then out := out.push pa
    else if samePtr pa pp || pa.isEmpty then out := out.push pb
    else none
  pure { base := p.base, pieces := out, count := max a.count b.count }

/-- Two stores grown from `p`: segments by where they start, each changed by
at most one of them, or with pieces changed by at most one; and what each
began of its own. -/
def mergeStore {α : Type} (p a b : Store α) : Option (Store α) := do
  if samePtr a p then return b
  if samePtr b p then return a
  let bases := ((a.segs ++ b.segs).toList.map (·.base)).eraseDups.mergeSort (· ≤ ·)
  let find := fun (s : Store α) (base : Nat) => s.segs.find? (·.base == base)
  let mut out : Array (Seg α) := #[]
  for base in bases do
    match find p base, find a base, find b base with
    | some sp, some sa, some sb => out := out.push (← mergeSeg sp sa sb)
    | none, some sa, none => out := out.push sa
    | none, none, some sb => out := out.push sb
    | _, _, _ => none
  match out.back? with
  | some last => pure { older := out.pop, last }
  | none => pure {}

/-- Two maps grown from `p`: an entry changed by at most one of them. -/
def mergeMap {κ ν : Type} [BEq κ] [Hashable κ] (p a b : Std.HashMap κ ν) : Option (Std.HashMap κ ν) :=
  if samePtr a p then some b else if samePtr b p then some a else
  b.fold (init := some a) fun acc key val => acc.bind fun m =>
    match p.get? key, a.get? key with
    | some pv, some av =>
      if samePtr val pv then some m else if samePtr av pv then some (m.insert key val) else none
    | some _, none => none
    | none, some av => if samePtr av val then some m else none
    | none, none => some (m.insert key val)

/-- Two sets grown from `p`. -/
def mergeSet {κ : Type} [BEq κ] [Hashable κ] (p a b : Std.HashSet κ) : Option (Std.HashSet κ) :=
  if samePtr a p then some b else if samePtr b p then some a else
  some (b.fold (init := a) fun m x => m.insert x)

/-- The state after checking `b`'s units after `a`'s, both having gone on
from `p`, where it can be put together from what each added. -/
def mergeStates (p a b : St) : Option St := do
  let tys ← mergeStore p.tys a.tys b.tys
  let rows ← mergeStore p.rows a.rows b.rows
  let mono ← mergeList p.mono a.mono b.mono
  let monoRows ← mergeList p.monoRows a.monoRows b.monoRows
  let monoCaps ← mergeList p.monoCaps a.monoCaps b.monoCaps
  let caps ← mergeStore p.caps a.caps b.caps
  let capEdges ← mergeStore p.capEdges a.capEdges b.capEdges
  let capOut ← mergeStore p.capOut a.capOut b.capOut
  let capEdgeNames ← mergeStore p.capEdgeNames a.capEdgeNames b.capEdgeNames
  let dups ← mergeArr p.dups a.dups b.dups
  let lateDups ← mergeArr p.lateDups a.lateDups b.lateDups
  let drops ← mergeArr p.drops a.drops b.drops
  let lateDrops ← mergeArr p.lateDrops a.lateDrops b.lateDrops
  let stays ← mergeArr p.stays a.stays b.stays
  let lateStays ← mergeArr p.lateStays a.lateStays b.lateStays
  let useDecls ← mergeList p.useDecls a.useDecls b.useDecls
  let movedCells ← mergeList p.movedCells a.movedCells b.movedCells
  let flagged ← mergeList p.flagged a.flagged b.flagged
  let givenSites ← mergeList p.givenSites a.givenSites b.givenSites
  let givenEdges ← mergeSet p.givenEdges a.givenEdges b.givenEdges
  let givers ← mergeList p.givers a.givers b.givers
  let givenReads ← mergeArr p.givenReads a.givenReads b.givenReads
  let aparts ← mergeArr p.aparts a.aparts b.aparts
  unless samePtr a.modules b.modules || samePtr a.modules p.modules || samePtr b.modules p.modules do none
  let fieldNames ← mergeList p.fieldNames a.fieldNames b.fieldNames
  let dotChosen ← mergeList p.dotChosen a.dotChosen b.dotChosen
  let argsChosen ← mergeList p.argsChosen a.argsChosen b.argsChosen
  let traitShape ← mergeList p.traitShape a.traitShape b.traitShape
  let assocUses ← mergeArr p.assocUses a.assocUses b.assocUses
  let writtenArgs ← mergeList p.writtenArgs a.writtenArgs b.writtenArgs
  let supers ← mergeList p.supers a.supers b.supers
  let ranked ← mergeList p.ranked a.ranked b.ranked
  let packs ← mergeArr p.packs a.packs b.packs
  let envGroups ← mergeArr p.envGroups a.envGroups b.envGroups
  let envAfter ← mergeArr p.envAfter a.envAfter b.envAfter
  let envLent ← mergeArr p.envLent a.envLent b.envLent
  let fnGroups ← mergeList p.fnGroups a.fnGroups b.fnGroups
  let envFns ← mergeList p.envFns a.envFns b.envFns
  let envLinks ← mergeArr p.envLinks a.envLinks b.envLinks
  let envWraps ← mergeArr p.envWraps a.envWraps b.envWraps
  let envMust ← mergeList p.envMust a.envMust b.envMust
  let envHeld ← mergeArr p.envHeld a.envHeld b.envHeld
  let derefReads ← mergeArr p.derefReads a.derefReads b.derefReads
  let rowChecks ← mergeList p.rowChecks a.rowChecks b.rowChecks
  let typeBounds ← mergeList p.typeBounds a.typeBounds b.typeBounds
  let typeParams ← mergeList p.typeParams a.typeParams b.typeParams
  let fieldReads ← mergeArr p.fieldReads a.fieldReads b.fieldReads
  let fieldSites ← mergeArr p.fieldSites a.fieldSites b.fieldSites
  let fieldTable ← mergeArr p.fieldTable a.fieldTable b.fieldTable
  let calls ← mergeArr p.calls a.calls b.calls
  let instRows ← mergeList p.instRows a.instRows b.instRows
  let unrunGiven ← mergeArr p.unrunGiven a.unrunGiven b.unrunGiven
  let sharedEdges ← mergeSet p.sharedEdges a.sharedEdges b.sharedEdges
  let assumedLinks ← mergeArr p.assumedLinks a.assumedLinks b.assumedLinks
  let abandoned ← mergeArr p.abandoned a.abandoned b.abandoned
  let sure ← mergeSet p.sure a.sure b.sure
  let lowerChecks ← mergeArr p.lowerChecks a.lowerChecks b.lowerChecks
  let fnBodies ← mergeList p.fnBodies a.fnBodies b.fnBodies
  let runFns ← mergeMap p.runFns a.runFns b.runFns
  let runCtors ← mergeSet p.runCtors a.runCtors b.runCtors
  let runAliases ← mergeMap p.runAliases a.runAliases b.runAliases
  let runOps ← mergeMap p.runOps a.runOps b.runOps
  let runExact ← mergeSet p.runExact a.runExact b.runExact
  let runNow ← mergeSet p.runNow a.runNow b.runNow
  let rowIncl ← mergeArr p.rowIncl a.rowIncl b.rowIncl
  let types ← mergeList p.types a.types b.types
  let ctors ← mergeList p.ctors a.ctors b.ctors
  let ops ← mergeList p.ops a.ops b.ops
  let effects ← mergeList p.effects a.effects b.effects
  let aliases ← mergeList p.aliases a.aliases b.aliases
  let fns ← mergeList p.fns a.fns b.fns
  let pending ← mergeArr p.pending a.pending b.pending
  let projections ← mergeArr p.projections a.projections b.projections
  let namedReads ← mergeArr p.namedReads a.namedReads b.namedReads
  let blockCaps ← mergeArr p.blockCaps a.blockCaps b.blockCaps
  let given ← mergeArr p.given a.given b.given
  let unrun ← mergeArr p.unrun a.unrun b.unrun
  let coercing ← mergeList p.coercing a.coercing b.coercing
  let coercions ← mergeArr p.coercions a.coercions b.coercions
  let loans ← mergeStore p.loans a.loans b.loans
  let cells ← mergeArr p.cells a.cells b.cells
  let bindSites ← mergeList p.bindSites a.bindSites b.bindSites
  let leftBehind ← mergeArr p.leftBehind a.leftBehind b.leftBehind
  let takenApart ← mergeArr p.takenApart a.takenApart b.takenApart
  let partReads ← mergeArr p.partReads a.partReads b.partReads
  let uses ← mergeArr p.uses a.uses b.uses
  let heldMoves ← mergeArr p.heldMoves a.heldMoves b.heldMoves
  let traits ← mergeList p.traits a.traits b.traits
  let methods ← mergeList p.methods a.methods b.methods
  let kimpls ← mergeList p.kimpls a.kimpls b.kimpls
  let blanketTraits ← mergeList p.blanketTraits a.blanketTraits b.blanketTraits
  let instSites ← mergeArr p.instSites a.instSites b.instSites
  let siteTable ← mergeList p.siteTable a.siteTable b.siteTable
  let siteTypes ← mergeList p.siteTypes a.siteTypes b.siteTypes
  let bounds ← mergeArr p.bounds a.bounds b.bounds
  let groupUses ← mergeArr p.groupUses a.groupUses b.groupUses
  let rigidKeys ← mergeStore p.rigidKeys a.rigidKeys b.rigidKeys
  let dropCands ← mergeArr p.dropCands a.dropCands b.dropCands
  let unsafeFns ← mergeList p.unsafeFns a.unsafeFns b.unsafeFns
  let dropSites ← mergeArr p.dropSites a.dropSites b.dropSites
  let lateKeeps ← mergeArr p.lateKeeps a.lateKeeps b.lateKeeps
  let quiets ← mergeArr p.quiets a.quiets b.quiets
  let paramTraits ← mergeList p.paramTraits a.paramTraits b.paramTraits
  let gatOccs ← mergeArr p.gatOccs a.gatOccs b.gatOccs
  let gatHolds ← mergeArr p.gatHolds a.gatHolds b.gatHolds
  unless samePtr a.dropMode b.dropMode || samePtr a.dropMode p.dropMode || samePtr b.dropMode p.dropMode do none
  let dictTable ← mergeArr p.dictTable a.dictTable b.dictTable
  let methodCalls ← mergeArr p.methodCalls a.methodCalls b.methodCalls
  let fnBounds ← mergeList p.fnBounds a.fnBounds b.fnBounds
  let impls ← mergeArr p.impls a.impls b.impls
  -- (An implementation's place: `b`'s come after `a`'s.)
  let shift := a.impls.size - p.impls.size
  let implsByBase := b.implsByBase.fold (init := a.implsByBase) fun m key is =>
    let mine := (is.filter (· ≥ p.impls.size)).map (· + shift)
    if mine.isEmpty then m else m.insert key ((m.getD key #[]) ++ mine)
  pure { p with
    tys,
    rows,
    mono,
    monoRows,
    monoCaps,
    caps,
    capEdges,
    capOut,
    capEdgeNames,
    brands := max a.brands b.brands,
    seen := b.seen,
    dups,
    lateDups,
    drops,
    lateDrops,
    stays,
    lateStays,
    useDecls,
    anyMust := a.anyMust || b.anyMust,
    anon := b.anon,
    rigidCaps := b.rigidCaps,
    givingBack := b.givingBack,
    movedCells,
    flagged,
    givenSites,
    givenEdges,
    givers,
    givenReads,
    aparts,
    outlives := b.outlives,
    staticCap := b.staticCap,
    modules := a.modules,
    fieldNames,
    rigidParams := b.rigidParams,
    dotChosen,
    argsChosen,
    wantResult := b.wantResult,
    traitShape,
    assocUses,
    writtenArgs,
    supers,
    ranked,
    elided := b.elided,
    packs,
    envGroups,
    envAfter,
    envLent,
    fnGroups,
    envFns,
    envLinks,
    envWraps,
    envMust,
    envHeld,
    derefReads,
    rowChecks,
    typeBounds,
    typeParams,
    instWith := b.instWith,
    fieldReads,
    fieldSites,
    fieldTable,
    firstSaid := b.firstSaid,
    calls,
    instRows,
    unrunGiven,
    sharedEdges,
    assumedLinks,
    abandoned,
    sure,
    lowerChecks,
    fnBodies,
    runFns,
    runCtors,
    runAliases,
    runOps,
    runExact,
    runNow,
    rowIncl,
    types,
    ctors,
    ops,
    effects,
    aliases,
    fns,
    group := b.group,
    pending,
    projections,
    namedReads,
    pos := b.pos,
    blockCaps,
    given,
    unrun,
    coercing,
    coercions,
    owner := b.owner,
    later := b.later,
    temps := b.temps,
    loans,
    cells,
    shapes := a.shapes || b.shapes,
    bindSites,
    leftBehind,
    takenApart,
    partReads,
    uses,
    heldMoves,
    traits,
    methods,
    impls,
    implsByBase,
    kimpls,
    lastBounds := b.lastBounds,
    patterned := a.patterned || b.patterned,
    blanketTraits,
    lastSites := b.lastSites,
    instSites,
    siteTable,
    siteTypes,
    bounds,
    groupUses,
    rigidKeys,
    implGivens := b.implGivens,
    dropCands,
    unsafeFns,
    unsafeBlock := b.unsafeBlock,
    arrayType := b.arrayType,
    dropSites,
    wildAt := b.wildAt,
    wildCount := b.wildCount,
    wildLet := b.wildLet,
    letBinds := b.letBinds,
    lateKeeps,
    quiets,
    gatScope := b.gatScope,
    projecting := b.projecting,
    ownItems := b.ownItems,
    paramTraits,
    gatOccs,
    gatHolds,
    dropMode := a.dropMode,
    dropAsked := max a.dropAsked b.dropAsked,
    dictTable,
    methodCalls,
    fnBounds }

end Glorious.Check
